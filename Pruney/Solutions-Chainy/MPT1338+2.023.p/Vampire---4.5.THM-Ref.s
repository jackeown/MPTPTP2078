%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 517 expanded)
%              Number of leaves         :   65 ( 253 expanded)
%              Depth                    :   11
%              Number of atoms          :  786 (2035 expanded)
%              Number of equality atoms :  158 ( 524 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f134,f139,f175,f181,f187,f193,f199,f240,f241,f242,f243,f244,f255,f264,f272,f290,f316,f340,f359,f367,f404,f409,f414,f436,f463,f469,f506,f511,f516,f597,f631,f662,f692,f694,f695,f698,f699])).

fof(f699,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) != k2_relat_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f698,plain,
    ( u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | k2_funct_1(sK3) != k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) != k2_relat_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK2) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f695,plain,
    ( k2_funct_1(sK3) != k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK3) = k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f694,plain,
    ( k2_funct_1(sK3) != k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | u1_struct_0(sK2) != k2_struct_0(sK2)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) != k2_relat_1(sK3)
    | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | k2_struct_0(sK1) != k1_relat_1(sK3)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f692,plain,
    ( spl4_78
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_61
    | ~ spl4_62
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f685,f513,f508,f503,f99,f79,f689])).

fof(f689,plain,
    ( spl4_78
  <=> k2_funct_1(sK3) = k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f79,plain,
    ( spl4_3
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f99,plain,
    ( spl4_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f503,plain,
    ( spl4_61
  <=> k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f508,plain,
    ( spl4_62
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f513,plain,
    ( spl4_63
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f685,plain,
    ( k2_funct_1(sK3) = k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_61
    | ~ spl4_62
    | ~ spl4_63 ),
    inference(unit_resulting_resolution,[],[f101,f81,f515,f510,f505,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f505,plain,
    ( k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f503])).

fof(f510,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f508])).

fof(f515,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f513])).

fof(f81,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f101,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f662,plain,
    ( ~ spl4_76
    | ~ spl4_77
    | spl4_23
    | ~ spl4_43
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f653,f466,f362,f211,f659,f655])).

fof(f655,plain,
    ( spl4_76
  <=> k1_relat_1(sK3) = k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f659,plain,
    ( spl4_77
  <=> m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f211,plain,
    ( spl4_23
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f362,plain,
    ( spl4_43
  <=> k2_struct_0(sK2) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f466,plain,
    ( spl4_56
  <=> k2_struct_0(sK1) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f653,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | k1_relat_1(sK3) != k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3))
    | spl4_23
    | ~ spl4_43
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f652,f364])).

fof(f364,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f362])).

fof(f652,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k1_relat_1(sK3))))
    | k1_relat_1(sK3) != k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3))
    | spl4_23
    | ~ spl4_43
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f651,f468])).

fof(f468,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f466])).

fof(f651,plain,
    ( k1_relat_1(sK3) != k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | spl4_23
    | ~ spl4_43
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f650,f468])).

fof(f650,plain,
    ( k2_struct_0(sK1) != k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | spl4_23
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f354,f364])).

fof(f354,plain,
    ( k2_struct_0(sK1) != k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | spl4_23 ),
    inference(superposition,[],[f213,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f213,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f631,plain,
    ( spl4_74
    | ~ spl4_70 ),
    inference(avatar_split_clause,[],[f609,f594,f628])).

fof(f628,plain,
    ( spl4_74
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f594,plain,
    ( spl4_70
  <=> sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f609,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ spl4_70 ),
    inference(unit_resulting_resolution,[],[f596,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f596,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f594])).

fof(f597,plain,
    ( spl4_70
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_61
    | ~ spl4_62
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f592,f513,f508,f503,f99,f79,f594])).

fof(f592,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_61
    | ~ spl4_62
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f591,f101])).

fof(f591,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_61
    | ~ spl4_62
    | ~ spl4_63 ),
    inference(subsumption_resolution,[],[f585,f515])).

fof(f585,plain,
    ( sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_61
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f584,f81])).

fof(f584,plain,
    ( ~ v2_funct_1(sK3)
    | sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_61
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f576,f505])).

fof(f576,plain,
    ( k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ v2_funct_1(sK3)
    | sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_62 ),
    inference(resolution,[],[f510,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP0(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f30,f33])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f516,plain,
    ( spl4_63
    | ~ spl4_49
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f477,f466,f406,f513])).

fof(f406,plain,
    ( spl4_49
  <=> v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f477,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_49
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f408,f468])).

fof(f408,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f406])).

fof(f511,plain,
    ( spl4_62
    | ~ spl4_48
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f476,f466,f401,f508])).

fof(f401,plain,
    ( spl4_48
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f476,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_48
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f403,f468])).

fof(f403,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f401])).

fof(f506,plain,
    ( spl4_61
    | ~ spl4_47
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f475,f466,f396,f503])).

fof(f396,plain,
    ( spl4_47
  <=> k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f475,plain,
    ( k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_47
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f398,f468])).

fof(f398,plain,
    ( k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f396])).

fof(f469,plain,
    ( spl4_56
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f464,f454,f268,f260,f466])).

fof(f260,plain,
    ( spl4_29
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f268,plain,
    ( spl4_30
  <=> v4_relat_1(sK3,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f454,plain,
    ( spl4_55
  <=> v1_partfun1(sK3,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f464,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_55 ),
    inference(unit_resulting_resolution,[],[f262,f270,f456,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f456,plain,
    ( v1_partfun1(sK3,k2_struct_0(sK1))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f454])).

fof(f270,plain,
    ( v4_relat_1(sK3,k2_struct_0(sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f268])).

fof(f262,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f260])).

fof(f463,plain,
    ( spl4_55
    | ~ spl4_7
    | ~ spl4_48
    | ~ spl4_49
    | spl4_50 ),
    inference(avatar_split_clause,[],[f462,f411,f406,f401,f99,f454])).

fof(f411,plain,
    ( spl4_50
  <=> v1_xboole_0(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f462,plain,
    ( v1_partfun1(sK3,k2_struct_0(sK1))
    | ~ spl4_7
    | ~ spl4_48
    | ~ spl4_49
    | spl4_50 ),
    inference(subsumption_resolution,[],[f461,f413])).

fof(f413,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | spl4_50 ),
    inference(avatar_component_clause,[],[f411])).

fof(f461,plain,
    ( v1_partfun1(sK3,k2_struct_0(sK1))
    | v1_xboole_0(k2_relat_1(sK3))
    | ~ spl4_7
    | ~ spl4_48
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f460,f101])).

fof(f460,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,k2_struct_0(sK1))
    | v1_xboole_0(k2_relat_1(sK3))
    | ~ spl4_48
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f452,f408])).

fof(f452,plain,
    ( ~ v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,k2_struct_0(sK1))
    | v1_xboole_0(k2_relat_1(sK3))
    | ~ spl4_48 ),
    inference(resolution,[],[f55,f403])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f436,plain,
    ( spl4_47
    | ~ spl4_42
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f435,f362,f356,f396])).

fof(f356,plain,
    ( spl4_42
  <=> k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f435,plain,
    ( k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)
    | ~ spl4_42
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f358,f364])).

fof(f358,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f356])).

fof(f414,plain,
    ( ~ spl4_50
    | spl4_28
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f374,f362,f252,f411])).

fof(f252,plain,
    ( spl4_28
  <=> v1_xboole_0(k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f374,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | spl4_28
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f254,f364])).

fof(f254,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f252])).

fof(f409,plain,
    ( spl4_49
    | ~ spl4_27
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f373,f362,f231,f406])).

fof(f231,plain,
    ( spl4_27
  <=> v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f373,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))
    | ~ spl4_27
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f233,f364])).

fof(f233,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f231])).

fof(f404,plain,
    ( spl4_48
    | ~ spl4_26
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f372,f362,f226,f401])).

fof(f226,plain,
    ( spl4_26
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f372,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))
    | ~ spl4_26
    | ~ spl4_43 ),
    inference(backward_demodulation,[],[f228,f364])).

fof(f228,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f226])).

fof(f367,plain,
    ( spl4_43
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f366,f226,f221,f362])).

fof(f221,plain,
    ( spl4_25
  <=> k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f366,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3)
    | ~ spl4_25
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f353,f228])).

fof(f353,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | ~ spl4_25 ),
    inference(superposition,[],[f223,f60])).

fof(f223,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f221])).

fof(f359,plain,
    ( spl4_42
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f351,f226,f356])).

fof(f351,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f228,f60])).

fof(f340,plain,
    ( ~ spl4_38
    | ~ spl4_39
    | spl4_24 ),
    inference(avatar_split_clause,[],[f326,f216,f337,f333])).

fof(f333,plain,
    ( spl4_38
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f337,plain,
    ( spl4_39
  <=> k2_struct_0(sK2) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f216,plain,
    ( spl4_24
  <=> k2_struct_0(sK2) = k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f326,plain,
    ( k2_struct_0(sK2) != k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))
    | spl4_24 ),
    inference(superposition,[],[f218,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f218,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f316,plain,
    ( spl4_36
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f311,f260,f99,f79,f313])).

fof(f313,plain,
    ( spl4_36
  <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f311,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f262,f101,f81,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f290,plain,
    ( spl4_32
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(avatar_split_clause,[],[f284,f260,f99,f79,f287])).

fof(f287,plain,
    ( spl4_32
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f284,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_7
    | ~ spl4_29 ),
    inference(unit_resulting_resolution,[],[f262,f101,f81,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f272,plain,
    ( spl4_30
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f266,f226,f268])).

fof(f266,plain,
    ( v4_relat_1(sK3,k2_struct_0(sK1))
    | ~ spl4_26 ),
    inference(resolution,[],[f61,f228])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f264,plain,
    ( spl4_29
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f258,f226,f260])).

fof(f258,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_26 ),
    inference(resolution,[],[f58,f228])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f255,plain,
    ( ~ spl4_28
    | ~ spl4_8
    | spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f250,f136,f109,f104,f252])).

fof(f104,plain,
    ( spl4_8
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f109,plain,
    ( spl4_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f136,plain,
    ( spl4_12
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f250,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK2))
    | ~ spl4_8
    | spl4_9
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f245,f138])).

fof(f138,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f245,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl4_8
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f111,f106,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f106,plain,
    ( l1_struct_0(sK2)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f244,plain,
    ( spl4_27
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f239,f196,f131,f231])).

fof(f131,plain,
    ( spl4_11
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f196,plain,
    ( spl4_22
  <=> v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f239,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(backward_demodulation,[],[f198,f133])).

fof(f133,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f198,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f196])).

fof(f243,plain,
    ( spl4_26
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f238,f190,f131,f226])).

fof(f190,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f238,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f192,f133])).

fof(f192,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2))))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f242,plain,
    ( spl4_25
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f237,f184,f131,f221])).

fof(f184,plain,
    ( spl4_20
  <=> k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f237,plain,
    ( k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)
    | ~ spl4_11
    | ~ spl4_20 ),
    inference(backward_demodulation,[],[f186,f133])).

fof(f186,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f184])).

fof(f241,plain,
    ( ~ spl4_24
    | ~ spl4_11
    | spl4_19 ),
    inference(avatar_split_clause,[],[f236,f178,f131,f216])).

fof(f178,plain,
    ( spl4_19
  <=> k2_struct_0(sK2) = k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f236,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | ~ spl4_11
    | spl4_19 ),
    inference(backward_demodulation,[],[f180,f133])).

fof(f180,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f240,plain,
    ( ~ spl4_23
    | ~ spl4_11
    | spl4_18 ),
    inference(avatar_split_clause,[],[f235,f172,f131,f211])).

fof(f172,plain,
    ( spl4_18
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f235,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))
    | ~ spl4_11
    | spl4_18 ),
    inference(backward_demodulation,[],[f174,f133])).

fof(f174,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f199,plain,
    ( spl4_22
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f194,f104,f94,f196])).

fof(f94,plain,
    ( spl4_6
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f194,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f129,f106])).

fof(f129,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f96,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f96,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f193,plain,
    ( spl4_21
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f188,f104,f89,f190])).

fof(f89,plain,
    ( spl4_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2))))
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f128,f106])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2))))
    | ~ l1_struct_0(sK2)
    | ~ spl4_5 ),
    inference(superposition,[],[f91,f50])).

fof(f91,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f187,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f182,f104,f84,f184])).

fof(f84,plain,
    ( spl4_4
  <=> k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f182,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3)
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f127,f106])).

fof(f127,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f86,f50])).

fof(f86,plain,
    ( k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f181,plain,
    ( ~ spl4_19
    | spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f176,f104,f70,f178])).

fof(f70,plain,
    ( spl4_1
  <=> k2_struct_0(sK2) = k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f176,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))
    | spl4_1
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f126,f106])).

fof(f126,plain,
    ( k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))
    | ~ l1_struct_0(sK2)
    | spl4_1 ),
    inference(superposition,[],[f72,f50])).

fof(f72,plain,
    ( k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f175,plain,
    ( ~ spl4_18
    | spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f170,f104,f74,f172])).

fof(f74,plain,
    ( spl4_2
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f170,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))
    | spl4_2
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f125,f106])).

fof(f125,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))
    | ~ l1_struct_0(sK2)
    | spl4_2 ),
    inference(superposition,[],[f76,f50])).

fof(f76,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f139,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f118,f104,f136])).

fof(f118,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f106,f50])).

fof(f134,plain,
    ( spl4_11
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f119,f114,f131])).

fof(f114,plain,
    ( spl4_10
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f119,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f116,f50])).

fof(f116,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f41,f114])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
      | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
    & v2_funct_1(sK3)
    & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f37,f36,f35])).

fof(f35,plain,
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
              ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))
            | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_struct_0(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))
          | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
        | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) )
      & v2_funct_1(sK3)
      & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f112,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f42,f109])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f43,f104])).

fof(f43,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f44,f99])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f45,f94])).

fof(f45,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f46,f89])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f82,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f48,f79])).

fof(f48,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f49,f74,f70])).

fof(f49,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:30:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (10832)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (10830)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (10822)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (10832)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f702,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f134,f139,f175,f181,f187,f193,f199,f240,f241,f242,f243,f244,f255,f264,f272,f290,f316,f340,f359,f367,f404,f409,f414,f436,f463,f469,f506,f511,f516,f597,f631,f662,f692,f694,f695,f698,f699])).
% 0.21/0.48  fof(f699,plain,(
% 0.21/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) != k2_relat_1(sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) | k2_struct_0(sK1) != k1_relat_1(sK3) | m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f698,plain,(
% 0.21/0.48    u1_struct_0(sK2) != k2_struct_0(sK2) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k1_relat_1(sK3) | k2_funct_1(sK3) != k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) != k2_relat_1(sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) | k2_struct_0(sK2) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f695,plain,(
% 0.21/0.48    k2_funct_1(sK3) != k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | k1_relat_1(sK3) != k2_relat_1(k2_funct_1(sK3)) | k1_relat_1(sK3) = k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f694,plain,(
% 0.21/0.48    k2_funct_1(sK3) != k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | u1_struct_0(sK2) != k2_struct_0(sK2) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) != k2_relat_1(sK3) | k2_struct_0(sK2) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) | k2_struct_0(sK1) != k1_relat_1(sK3) | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f692,plain,(
% 0.21/0.48    spl4_78 | ~spl4_3 | ~spl4_7 | ~spl4_61 | ~spl4_62 | ~spl4_63),
% 0.21/0.48    inference(avatar_split_clause,[],[f685,f513,f508,f503,f99,f79,f689])).
% 0.21/0.48  fof(f689,plain,(
% 0.21/0.48    spl4_78 <=> k2_funct_1(sK3) = k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    spl4_3 <=> v2_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl4_7 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f503,plain,(
% 0.21/0.48    spl4_61 <=> k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 0.21/0.48  fof(f508,plain,(
% 0.21/0.48    spl4_62 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.21/0.48  fof(f513,plain,(
% 0.21/0.48    spl4_63 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.21/0.48  fof(f685,plain,(
% 0.21/0.48    k2_funct_1(sK3) = k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | (~spl4_3 | ~spl4_7 | ~spl4_61 | ~spl4_62 | ~spl4_63)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f101,f81,f515,f510,f505,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.48  fof(f505,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_61),
% 0.21/0.48    inference(avatar_component_clause,[],[f503])).
% 0.21/0.48  fof(f510,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_62),
% 0.21/0.48    inference(avatar_component_clause,[],[f508])).
% 0.21/0.48  fof(f515,plain,(
% 0.21/0.48    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_63),
% 0.21/0.48    inference(avatar_component_clause,[],[f513])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    v2_funct_1(sK3) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f79])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f662,plain,(
% 0.21/0.48    ~spl4_76 | ~spl4_77 | spl4_23 | ~spl4_43 | ~spl4_56),
% 0.21/0.48    inference(avatar_split_clause,[],[f653,f466,f362,f211,f659,f655])).
% 0.21/0.48  fof(f655,plain,(
% 0.21/0.48    spl4_76 <=> k1_relat_1(sK3) = k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 0.21/0.48  fof(f659,plain,(
% 0.21/0.48    spl4_77 <=> m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    spl4_23 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.48  fof(f362,plain,(
% 0.21/0.48    spl4_43 <=> k2_struct_0(sK2) = k2_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.21/0.48  fof(f466,plain,(
% 0.21/0.48    spl4_56 <=> k2_struct_0(sK1) = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.48  fof(f653,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | k1_relat_1(sK3) != k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)) | (spl4_23 | ~spl4_43 | ~spl4_56)),
% 0.21/0.48    inference(forward_demodulation,[],[f652,f364])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relat_1(sK3) | ~spl4_43),
% 0.21/0.48    inference(avatar_component_clause,[],[f362])).
% 0.21/0.48  fof(f652,plain,(
% 0.21/0.48    ~m1_subset_1(k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k1_relat_1(sK3)))) | k1_relat_1(sK3) != k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)) | (spl4_23 | ~spl4_43 | ~spl4_56)),
% 0.21/0.48    inference(forward_demodulation,[],[f651,f468])).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    k2_struct_0(sK1) = k1_relat_1(sK3) | ~spl4_56),
% 0.21/0.48    inference(avatar_component_clause,[],[f466])).
% 0.21/0.48  fof(f651,plain,(
% 0.21/0.48    k1_relat_1(sK3) != k2_relat_1(k2_tops_2(k1_relat_1(sK3),k2_relat_1(sK3),sK3)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | (spl4_23 | ~spl4_43 | ~spl4_56)),
% 0.21/0.48    inference(forward_demodulation,[],[f650,f468])).
% 0.21/0.48  fof(f650,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_relat_1(sK3),sK3)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | (spl4_23 | ~spl4_43)),
% 0.21/0.48    inference(forward_demodulation,[],[f354,f364])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | spl4_23),
% 0.21/0.48    inference(superposition,[],[f213,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | spl4_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f211])).
% 0.21/0.48  fof(f631,plain,(
% 0.21/0.48    spl4_74 | ~spl4_70),
% 0.21/0.48    inference(avatar_split_clause,[],[f609,f594,f628])).
% 0.21/0.48  fof(f628,plain,(
% 0.21/0.48    spl4_74 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.21/0.48  fof(f594,plain,(
% 0.21/0.48    spl4_70 <=> sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 0.21/0.48  fof(f609,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) | ~spl4_70),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f596,f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP0(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP0(X0,X1,X2))),
% 0.21/0.48    inference(nnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP0(X0,X1,X2))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f596,plain,(
% 0.21/0.48    sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_70),
% 0.21/0.48    inference(avatar_component_clause,[],[f594])).
% 0.21/0.48  fof(f597,plain,(
% 0.21/0.48    spl4_70 | ~spl4_3 | ~spl4_7 | ~spl4_61 | ~spl4_62 | ~spl4_63),
% 0.21/0.48    inference(avatar_split_clause,[],[f592,f513,f508,f503,f99,f79,f594])).
% 0.21/0.48  fof(f592,plain,(
% 0.21/0.48    sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | (~spl4_3 | ~spl4_7 | ~spl4_61 | ~spl4_62 | ~spl4_63)),
% 0.21/0.48    inference(subsumption_resolution,[],[f591,f101])).
% 0.21/0.48  fof(f591,plain,(
% 0.21/0.48    sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~v1_funct_1(sK3) | (~spl4_3 | ~spl4_61 | ~spl4_62 | ~spl4_63)),
% 0.21/0.48    inference(subsumption_resolution,[],[f585,f515])).
% 0.21/0.48  fof(f585,plain,(
% 0.21/0.48    sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl4_3 | ~spl4_61 | ~spl4_62)),
% 0.21/0.48    inference(subsumption_resolution,[],[f584,f81])).
% 0.21/0.48  fof(f584,plain,(
% 0.21/0.48    ~v2_funct_1(sK3) | sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | (~spl4_61 | ~spl4_62)),
% 0.21/0.48    inference(subsumption_resolution,[],[f576,f505])).
% 0.21/0.48  fof(f576,plain,(
% 0.21/0.48    k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~v2_funct_1(sK3) | sP0(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~spl4_62),
% 0.21/0.48    inference(resolution,[],[f510,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP0(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (sP0(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(definition_folding,[],[f30,f33])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.48  fof(f516,plain,(
% 0.21/0.48    spl4_63 | ~spl4_49 | ~spl4_56),
% 0.21/0.48    inference(avatar_split_clause,[],[f477,f466,f406,f513])).
% 0.21/0.48  fof(f406,plain,(
% 0.21/0.48    spl4_49 <=> v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.48  fof(f477,plain,(
% 0.21/0.48    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | (~spl4_49 | ~spl4_56)),
% 0.21/0.48    inference(backward_demodulation,[],[f408,f468])).
% 0.21/0.48  fof(f408,plain,(
% 0.21/0.48    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~spl4_49),
% 0.21/0.48    inference(avatar_component_clause,[],[f406])).
% 0.21/0.48  fof(f511,plain,(
% 0.21/0.48    spl4_62 | ~spl4_48 | ~spl4_56),
% 0.21/0.48    inference(avatar_split_clause,[],[f476,f466,f401,f508])).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    spl4_48 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.48  fof(f476,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | (~spl4_48 | ~spl4_56)),
% 0.21/0.48    inference(backward_demodulation,[],[f403,f468])).
% 0.21/0.48  fof(f403,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | ~spl4_48),
% 0.21/0.48    inference(avatar_component_clause,[],[f401])).
% 0.21/0.48  fof(f506,plain,(
% 0.21/0.48    spl4_61 | ~spl4_47 | ~spl4_56),
% 0.21/0.48    inference(avatar_split_clause,[],[f475,f466,f396,f503])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    spl4_47 <=> k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.48  fof(f475,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | (~spl4_47 | ~spl4_56)),
% 0.21/0.48    inference(backward_demodulation,[],[f398,f468])).
% 0.21/0.48  fof(f398,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | ~spl4_47),
% 0.21/0.48    inference(avatar_component_clause,[],[f396])).
% 0.21/0.48  fof(f469,plain,(
% 0.21/0.48    spl4_56 | ~spl4_29 | ~spl4_30 | ~spl4_55),
% 0.21/0.48    inference(avatar_split_clause,[],[f464,f454,f268,f260,f466])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    spl4_29 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    spl4_30 <=> v4_relat_1(sK3,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.48  fof(f454,plain,(
% 0.21/0.48    spl4_55 <=> v1_partfun1(sK3,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 0.21/0.48  fof(f464,plain,(
% 0.21/0.48    k2_struct_0(sK1) = k1_relat_1(sK3) | (~spl4_29 | ~spl4_30 | ~spl4_55)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f262,f270,f456,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.48  fof(f456,plain,(
% 0.21/0.48    v1_partfun1(sK3,k2_struct_0(sK1)) | ~spl4_55),
% 0.21/0.48    inference(avatar_component_clause,[],[f454])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    v4_relat_1(sK3,k2_struct_0(sK1)) | ~spl4_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f268])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl4_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f260])).
% 0.21/0.48  fof(f463,plain,(
% 0.21/0.48    spl4_55 | ~spl4_7 | ~spl4_48 | ~spl4_49 | spl4_50),
% 0.21/0.48    inference(avatar_split_clause,[],[f462,f411,f406,f401,f99,f454])).
% 0.21/0.48  fof(f411,plain,(
% 0.21/0.48    spl4_50 <=> v1_xboole_0(k2_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.48  fof(f462,plain,(
% 0.21/0.48    v1_partfun1(sK3,k2_struct_0(sK1)) | (~spl4_7 | ~spl4_48 | ~spl4_49 | spl4_50)),
% 0.21/0.48    inference(subsumption_resolution,[],[f461,f413])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_relat_1(sK3)) | spl4_50),
% 0.21/0.48    inference(avatar_component_clause,[],[f411])).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    v1_partfun1(sK3,k2_struct_0(sK1)) | v1_xboole_0(k2_relat_1(sK3)) | (~spl4_7 | ~spl4_48 | ~spl4_49)),
% 0.21/0.48    inference(subsumption_resolution,[],[f460,f101])).
% 0.21/0.48  fof(f460,plain,(
% 0.21/0.48    ~v1_funct_1(sK3) | v1_partfun1(sK3,k2_struct_0(sK1)) | v1_xboole_0(k2_relat_1(sK3)) | (~spl4_48 | ~spl4_49)),
% 0.21/0.48    inference(subsumption_resolution,[],[f452,f408])).
% 0.21/0.48  fof(f452,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | ~v1_funct_1(sK3) | v1_partfun1(sK3,k2_struct_0(sK1)) | v1_xboole_0(k2_relat_1(sK3)) | ~spl4_48),
% 0.21/0.48    inference(resolution,[],[f55,f403])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    spl4_47 | ~spl4_42 | ~spl4_43),
% 0.21/0.48    inference(avatar_split_clause,[],[f435,f362,f356,f396])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    spl4_42 <=> k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.48  fof(f435,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k2_relset_1(k2_struct_0(sK1),k2_relat_1(sK3),sK3) | (~spl4_42 | ~spl4_43)),
% 0.21/0.48    inference(forward_demodulation,[],[f358,f364])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) | ~spl4_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f356])).
% 0.21/0.48  fof(f414,plain,(
% 0.21/0.48    ~spl4_50 | spl4_28 | ~spl4_43),
% 0.21/0.48    inference(avatar_split_clause,[],[f374,f362,f252,f411])).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    spl4_28 <=> v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.48  fof(f374,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_relat_1(sK3)) | (spl4_28 | ~spl4_43)),
% 0.21/0.48    inference(backward_demodulation,[],[f254,f364])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK2)) | spl4_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f252])).
% 0.21/0.48  fof(f409,plain,(
% 0.21/0.48    spl4_49 | ~spl4_27 | ~spl4_43),
% 0.21/0.48    inference(avatar_split_clause,[],[f373,f362,f231,f406])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl4_27 <=> v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    v1_funct_2(sK3,k2_struct_0(sK1),k2_relat_1(sK3)) | (~spl4_27 | ~spl4_43)),
% 0.21/0.48    inference(backward_demodulation,[],[f233,f364])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl4_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f404,plain,(
% 0.21/0.48    spl4_48 | ~spl4_26 | ~spl4_43),
% 0.21/0.48    inference(avatar_split_clause,[],[f372,f362,f226,f401])).
% 0.21/0.48  fof(f226,plain,(
% 0.21/0.48    spl4_26 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.48  fof(f372,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_relat_1(sK3)))) | (~spl4_26 | ~spl4_43)),
% 0.21/0.48    inference(backward_demodulation,[],[f228,f364])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | ~spl4_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f226])).
% 0.21/0.48  fof(f367,plain,(
% 0.21/0.48    spl4_43 | ~spl4_25 | ~spl4_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f366,f226,f221,f362])).
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    spl4_25 <=> k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.48  fof(f366,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relat_1(sK3) | (~spl4_25 | ~spl4_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f353,f228])).
% 0.21/0.48  fof(f353,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | ~spl4_25),
% 0.21/0.48    inference(superposition,[],[f223,f60])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) | ~spl4_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f221])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    spl4_42 | ~spl4_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f351,f226,f356])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) | ~spl4_26),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f228,f60])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ~spl4_38 | ~spl4_39 | spl4_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f326,f216,f337,f333])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    spl4_38 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    spl4_39 <=> k2_struct_0(sK2) = k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    spl4_24 <=> k2_struct_0(sK2) = k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    k2_struct_0(sK2) != k1_relat_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK1)))) | spl4_24),
% 0.21/0.48    inference(superposition,[],[f218,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | spl4_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f216])).
% 0.21/0.48  fof(f316,plain,(
% 0.21/0.48    spl4_36 | ~spl4_3 | ~spl4_7 | ~spl4_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f311,f260,f99,f79,f313])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    spl4_36 <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.48  fof(f311,plain,(
% 0.21/0.48    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_3 | ~spl4_7 | ~spl4_29)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f262,f101,f81,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    spl4_32 | ~spl4_3 | ~spl4_7 | ~spl4_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f284,f260,f99,f79,f287])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    spl4_32 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | (~spl4_3 | ~spl4_7 | ~spl4_29)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f262,f101,f81,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    spl4_30 | ~spl4_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f266,f226,f268])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    v4_relat_1(sK3,k2_struct_0(sK1)) | ~spl4_26),
% 0.21/0.48    inference(resolution,[],[f61,f228])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    spl4_29 | ~spl4_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f258,f226,f260])).
% 0.21/0.48  fof(f258,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl4_26),
% 0.21/0.48    inference(resolution,[],[f58,f228])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    ~spl4_28 | ~spl4_8 | spl4_9 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f250,f136,f109,f104,f252])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_8 <=> l1_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    spl4_9 <=> v2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    spl4_12 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ~v1_xboole_0(k2_struct_0(sK2)) | (~spl4_8 | spl4_9 | ~spl4_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f245,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f136])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    ~v1_xboole_0(u1_struct_0(sK2)) | (~spl4_8 | spl4_9)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f111,f106,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    l1_struct_0(sK2) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~v2_struct_0(sK2) | spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f109])).
% 0.21/0.48  fof(f244,plain,(
% 0.21/0.48    spl4_27 | ~spl4_11 | ~spl4_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f239,f196,f131,f231])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl4_11 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    spl4_22 <=> v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) | (~spl4_11 | ~spl4_22)),
% 0.21/0.48    inference(backward_demodulation,[],[f198,f133])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2)) | ~spl4_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f196])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    spl4_26 | ~spl4_11 | ~spl4_21),
% 0.21/0.48    inference(avatar_split_clause,[],[f238,f190,f131,f226])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) | (~spl4_11 | ~spl4_21)),
% 0.21/0.48    inference(backward_demodulation,[],[f192,f133])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2)))) | ~spl4_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f190])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    spl4_25 | ~spl4_11 | ~spl4_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f237,f184,f131,f221])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    spl4_20 <=> k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) | (~spl4_11 | ~spl4_20)),
% 0.21/0.48    inference(backward_demodulation,[],[f186,f133])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3) | ~spl4_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f184])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    ~spl4_24 | ~spl4_11 | spl4_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f236,f178,f131,f216])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl4_19 <=> k2_struct_0(sK2) = k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | (~spl4_11 | spl4_19)),
% 0.21/0.48    inference(backward_demodulation,[],[f180,f133])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) | spl4_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f178])).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~spl4_23 | ~spl4_11 | spl4_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f235,f172,f131,f211])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    spl4_18 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) | (~spl4_11 | spl4_18)),
% 0.21/0.48    inference(backward_demodulation,[],[f174,f133])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) | spl4_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f172])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl4_22 | ~spl4_6 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f194,f104,f94,f196])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl4_6 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2)) | (~spl4_6 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f129,f106])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    v1_funct_2(sK3,u1_struct_0(sK1),k2_struct_0(sK2)) | ~l1_struct_0(sK2) | ~spl4_6),
% 0.21/0.48    inference(superposition,[],[f96,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl4_21 | ~spl4_5 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f188,f104,f89,f190])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl4_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2)))) | (~spl4_5 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f106])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK2)))) | ~l1_struct_0(sK2) | ~spl4_5),
% 0.21/0.48    inference(superposition,[],[f91,f50])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f89])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl4_20 | ~spl4_4 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f182,f104,f84,f184])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl4_4 <=> k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3) | (~spl4_4 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f106])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK2),sK3) | ~l1_struct_0(sK2) | ~spl4_4),
% 0.21/0.48    inference(superposition,[],[f86,f50])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ~spl4_19 | spl4_1 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f176,f104,f70,f178])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl4_1 <=> k2_struct_0(sK2) = k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) | (spl4_1 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f106])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    k2_struct_0(sK2) != k1_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) | ~l1_struct_0(sK2) | spl4_1),
% 0.21/0.49    inference(superposition,[],[f72,f50])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ~spl4_18 | spl4_2 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f170,f104,f74,f172])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl4_2 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) | (spl4_2 | ~spl4_8)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f106])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK2),sK3)) | ~l1_struct_0(sK2) | spl4_2),
% 0.21/0.49    inference(superposition,[],[f76,f50])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f74])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl4_12 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f118,f104,f136])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl4_8),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f106,f50])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl4_11 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f119,f114,f131])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_10 <=> l1_struct_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl4_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f116,f50])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    l1_struct_0(sK1) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f41,f114])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    l1_struct_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    (((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)) & l1_struct_0(sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f37,f36,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X2] : ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),X2))) & v2_funct_1(X2) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => ((k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) & v2_funct_1(sK3) & k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f12])).
% 0.21/0.49  fof(f12,conjecture,(
% 0.21/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f109])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~v2_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f104])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    l1_struct_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f99])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f94])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f89])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f84])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    k2_struct_0(sK2) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f79])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    v2_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f74,f70])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) | k2_struct_0(sK2) != k1_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f38])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10832)------------------------------
% 0.21/0.49  % (10832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10832)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10832)Memory used [KB]: 11129
% 0.21/0.49  % (10832)Time elapsed: 0.051 s
% 0.21/0.49  % (10832)------------------------------
% 0.21/0.49  % (10832)------------------------------
% 0.21/0.49  % (10815)Success in time 0.127 s
%------------------------------------------------------------------------------
