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
% DateTime   : Thu Dec  3 13:14:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  231 ( 469 expanded)
%              Number of leaves         :   61 ( 223 expanded)
%              Depth                    :   10
%              Number of atoms          :  882 (2089 expanded)
%              Number of equality atoms :  223 ( 586 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f109,f113,f117,f121,f125,f129,f135,f139,f153,f163,f170,f196,f200,f204,f229,f236,f249,f263,f267,f297,f308,f314,f362,f363,f369,f412,f426,f439,f449,f454,f458,f468,f472,f477,f496,f508,f509])).

fof(f509,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f508,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f496,plain,
    ( ~ spl3_46
    | spl3_55
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f492,f475,f303,f238,f156,f141,f494,f353])).

fof(f353,plain,
    ( spl3_46
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f494,plain,
    ( spl3_55
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f141,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f156,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f238,plain,
    ( spl3_30
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f303,plain,
    ( spl3_38
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f475,plain,
    ( spl3_54
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f492,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_54 ),
    inference(trivial_inequality_removal,[],[f491])).

fof(f491,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f490,f142])).

fof(f142,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f490,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f489,f304])).

fof(f304,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f303])).

fof(f489,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f488,f239])).

fof(f239,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f238])).

fof(f488,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f487,f304])).

fof(f487,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f484,f239])).

fof(f484,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_54 ),
    inference(resolution,[],[f476,f157])).

fof(f157,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( ~ spl3_7
    | spl3_54
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f473,f95,f475,f111])).

fof(f111,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f95,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f75,f96])).

fof(f96,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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

fof(f472,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f468,plain,
    ( ~ spl3_7
    | ~ spl3_46
    | ~ spl3_45
    | ~ spl3_3
    | ~ spl3_43
    | spl3_52 ),
    inference(avatar_split_clause,[],[f465,f447,f322,f95,f348,f353,f111])).

fof(f348,plain,
    ( spl3_45
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f322,plain,
    ( spl3_43
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f447,plain,
    ( spl3_52
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f465,plain,
    ( ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_43
    | spl3_52 ),
    inference(trivial_inequality_removal,[],[f464])).

fof(f464,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_43
    | spl3_52 ),
    inference(forward_demodulation,[],[f462,f323])).

fof(f323,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f322])).

fof(f462,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl3_52 ),
    inference(resolution,[],[f448,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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

fof(f448,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f447])).

fof(f458,plain,
    ( ~ spl3_23
    | ~ spl3_51
    | spl3_27
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f456,f227,f194,f221,f444,f208])).

fof(f208,plain,
    ( spl3_23
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f444,plain,
    ( spl3_51
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f221,plain,
    ( spl3_27
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f194,plain,
    ( spl3_22
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f227,plain,
    ( spl3_28
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f456,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f230,f195])).

fof(f195,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f194])).

fof(f230,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_28 ),
    inference(superposition,[],[f56,f228])).

fof(f228,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f227])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f454,plain,
    ( spl3_53
    | ~ spl3_28
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f450,f424,f227,f452])).

fof(f452,plain,
    ( spl3_53
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f424,plain,
    ( spl3_49
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f450,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_28
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f438,f228])).

fof(f438,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(resolution,[],[f425,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f425,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f424])).

fof(f449,plain,
    ( spl3_50
    | spl3_51
    | ~ spl3_52
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f437,f424,f447,f444,f441])).

fof(f441,plain,
    ( spl3_50
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f437,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(resolution,[],[f425,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f439,plain,
    ( spl3_23
    | ~ spl3_49 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl3_23
    | ~ spl3_49 ),
    inference(resolution,[],[f425,f224])).

fof(f224,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_23 ),
    inference(resolution,[],[f209,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f209,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f208])).

fof(f426,plain,
    ( ~ spl3_46
    | spl3_49
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f421,f410,f303,f238,f156,f141,f424,f353])).

fof(f410,plain,
    ( spl3_48
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f421,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f420,f239])).

fof(f420,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f419,f304])).

fof(f419,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_48 ),
    inference(trivial_inequality_removal,[],[f418])).

fof(f418,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f417,f142])).

fof(f417,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_38
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f416,f304])).

fof(f416,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f413,f239])).

fof(f413,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_16
    | ~ spl3_48 ),
    inference(resolution,[],[f411,f157])).

fof(f411,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f410])).

fof(f412,plain,
    ( ~ spl3_7
    | spl3_48
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f408,f95,f410,f111])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f74,f96])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f369,plain,
    ( ~ spl3_35
    | spl3_27
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f368,f312,f238,f156,f221,f265])).

fof(f265,plain,
    ( spl3_35
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f312,plain,
    ( spl3_40
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f368,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f367,f239])).

fof(f367,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_16
    | ~ spl3_30
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f365,f239])).

fof(f365,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_16
    | ~ spl3_40 ),
    inference(resolution,[],[f313,f157])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f312])).

fof(f363,plain,
    ( spl3_46
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f338,f303,f265,f353])).

fof(f338,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(superposition,[],[f266,f304])).

fof(f266,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f265])).

fof(f362,plain,
    ( spl3_45
    | ~ spl3_34
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f337,f303,f261,f348])).

fof(f261,plain,
    ( spl3_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f337,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_34
    | ~ spl3_38 ),
    inference(superposition,[],[f262,f304])).

fof(f262,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f261])).

fof(f314,plain,
    ( ~ spl3_7
    | spl3_40
    | spl3_39 ),
    inference(avatar_split_clause,[],[f310,f306,f312,f111])).

fof(f306,plain,
    ( spl3_39
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f310,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | ~ v1_funct_1(sK2) )
    | spl3_39 ),
    inference(resolution,[],[f307,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f307,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f306])).

fof(f308,plain,
    ( spl3_38
    | ~ spl3_39
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f300,f156,f306,f303])).

fof(f300,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f298,f157])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK2,X0)
        | k1_relat_1(sK2) = X0 )
    | ~ spl3_16 ),
    inference(resolution,[],[f284,f157])).

fof(f284,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f231,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f231,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f61,f63])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f297,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f267,plain,
    ( spl3_35
    | ~ spl3_17
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f253,f238,f161,f265])).

fof(f161,plain,
    ( spl3_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f253,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_17
    | ~ spl3_30 ),
    inference(superposition,[],[f162,f239])).

fof(f162,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f263,plain,
    ( spl3_34
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f252,f238,f156,f261])).

fof(f252,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_16
    | ~ spl3_30 ),
    inference(superposition,[],[f157,f239])).

fof(f249,plain,
    ( spl3_30
    | ~ spl3_14
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f247,f234,f141,f238])).

fof(f234,plain,
    ( spl3_29
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f247,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_29 ),
    inference(superposition,[],[f142,f235])).

fof(f235,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f234])).

fof(f236,plain,
    ( spl3_29
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f232,f156,f234])).

fof(f232,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f64,f157])).

fof(f229,plain,
    ( ~ spl3_21
    | ~ spl3_7
    | spl3_28
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f225,f95,f227,f111,f190])).

fof(f190,plain,
    ( spl3_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f225,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f60,f96])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f204,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f203,f137,f133,f103,f156])).

fof(f103,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f133,plain,
    ( spl3_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f137,plain,
    ( spl3_13
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f203,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f202,f138])).

fof(f138,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f202,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f104,f134])).

fof(f134,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f133])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f200,plain,
    ( ~ spl3_5
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | ~ spl3_5
    | spl3_21 ),
    inference(subsumption_resolution,[],[f104,f197])).

fof(f197,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_21 ),
    inference(resolution,[],[f191,f63])).

fof(f191,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f190])).

fof(f196,plain,
    ( ~ spl3_21
    | ~ spl3_7
    | spl3_22
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f188,f95,f194,f111,f190])).

fof(f188,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f59,f96])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f170,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_18
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f164,f133,f168,f115,f119])).

fof(f119,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f115,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f168,plain,
    ( spl3_18
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f164,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(superposition,[],[f58,f134])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f163,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f159,f137,f133,f107,f161])).

fof(f107,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f159,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f146,f138])).

fof(f146,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f108,f134])).

fof(f108,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f153,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f152,f137,f133,f99,f141])).

fof(f99,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f152,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f144,f138])).

fof(f144,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f100,f134])).

fof(f100,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f139,plain,
    ( spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f131,f123,f137])).

fof(f123,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f131,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f57,f124])).

fof(f124,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f123])).

fof(f57,plain,(
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

fof(f135,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f130,f115,f133])).

fof(f130,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f57,f116])).

fof(f116,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f129,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f54,f127])).

fof(f127,plain,
    ( spl3_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f125,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f45,f123])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f40,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
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
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f121,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f46,f119])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f47,f115])).

fof(f47,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f111])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f49,f107])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

% (3640)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f105,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f53,f91,f88])).

fof(f88,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f91,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (3629)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (3638)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (3630)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (3637)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (3630)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (3637)Refutation not found, incomplete strategy% (3637)------------------------------
% 0.22/0.49  % (3637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3637)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3637)Memory used [KB]: 1663
% 0.22/0.49  % (3637)Time elapsed: 0.072 s
% 0.22/0.49  % (3637)------------------------------
% 0.22/0.49  % (3637)------------------------------
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f510,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f109,f113,f117,f121,f125,f129,f135,f139,f153,f163,f170,f196,f200,f204,f229,f236,f249,f263,f267,f297,f308,f314,f362,f363,f369,f412,f426,f439,f449,f454,f458,f468,f472,f477,f496,f508,f509])).
% 0.22/0.50  fof(f509,plain,(
% 0.22/0.50    k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f508,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f496,plain,(
% 0.22/0.50    ~spl3_46 | spl3_55 | ~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_54),
% 0.22/0.50    inference(avatar_split_clause,[],[f492,f475,f303,f238,f156,f141,f494,f353])).
% 0.22/0.50  fof(f353,plain,(
% 0.22/0.50    spl3_46 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.50  fof(f494,plain,(
% 0.22/0.50    spl3_55 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl3_30 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f303,plain,(
% 0.22/0.50    spl3_38 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.50  fof(f475,plain,(
% 0.22/0.50    spl3_54 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.50  fof(f492,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_54)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f491])).
% 0.22/0.50  fof(f491,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f490,f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f490,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f489,f304])).
% 0.22/0.50  fof(f304,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f303])).
% 0.22/0.50  fof(f489,plain,(
% 0.22/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f488,f239])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f238])).
% 0.22/0.50  fof(f488,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f487,f304])).
% 0.22/0.50  fof(f487,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_30 | ~spl3_54)),
% 0.22/0.50    inference(forward_demodulation,[],[f484,f239])).
% 0.22/0.50  fof(f484,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_54)),
% 0.22/0.50    inference(resolution,[],[f476,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f476,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_54),
% 0.22/0.50    inference(avatar_component_clause,[],[f475])).
% 0.22/0.50  fof(f477,plain,(
% 0.22/0.50    ~spl3_7 | spl3_54 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f473,f95,f475,f111])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_7 <=> v1_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl3_3 <=> v2_funct_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f473,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f75,f96])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    v2_funct_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f95])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.50  fof(f472,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f468,plain,(
% 0.22/0.50    ~spl3_7 | ~spl3_46 | ~spl3_45 | ~spl3_3 | ~spl3_43 | spl3_52),
% 0.22/0.50    inference(avatar_split_clause,[],[f465,f447,f322,f95,f348,f353,f111])).
% 0.22/0.50  fof(f348,plain,(
% 0.22/0.50    spl3_45 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    spl3_43 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.50  fof(f447,plain,(
% 0.22/0.50    spl3_52 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_43 | spl3_52)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f464])).
% 0.22/0.50  fof(f464,plain,(
% 0.22/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_43 | spl3_52)),
% 0.22/0.50    inference(forward_demodulation,[],[f462,f323])).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_43),
% 0.22/0.50    inference(avatar_component_clause,[],[f322])).
% 0.22/0.50  fof(f462,plain,(
% 0.22/0.50    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | spl3_52),
% 0.22/0.50    inference(resolution,[],[f448,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.50  fof(f448,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | spl3_52),
% 0.22/0.50    inference(avatar_component_clause,[],[f447])).
% 0.22/0.50  fof(f458,plain,(
% 0.22/0.50    ~spl3_23 | ~spl3_51 | spl3_27 | ~spl3_22 | ~spl3_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f456,f227,f194,f221,f444,f208])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl3_23 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f444,plain,(
% 0.22/0.50    spl3_51 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    spl3_27 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    spl3_22 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    spl3_28 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f456,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_22 | ~spl3_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f230,f195])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f194])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    k1_xboole_0 != k1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_28),
% 0.22/0.50    inference(superposition,[],[f56,f228])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl3_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f227])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.22/0.50  fof(f454,plain,(
% 0.22/0.50    spl3_53 | ~spl3_28 | ~spl3_49),
% 0.22/0.50    inference(avatar_split_clause,[],[f450,f424,f227,f452])).
% 0.22/0.50  fof(f452,plain,(
% 0.22/0.50    spl3_53 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    spl3_49 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_28 | ~spl3_49)),
% 0.22/0.50    inference(forward_demodulation,[],[f438,f228])).
% 0.22/0.50  fof(f438,plain,(
% 0.22/0.50    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_49),
% 0.22/0.50    inference(resolution,[],[f425,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_49),
% 0.22/0.50    inference(avatar_component_clause,[],[f424])).
% 0.22/0.50  fof(f449,plain,(
% 0.22/0.50    spl3_50 | spl3_51 | ~spl3_52 | ~spl3_49),
% 0.22/0.50    inference(avatar_split_clause,[],[f437,f424,f447,f444,f441])).
% 0.22/0.50  fof(f441,plain,(
% 0.22/0.50    spl3_50 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.50  fof(f437,plain,(
% 0.22/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_49),
% 0.22/0.50    inference(resolution,[],[f425,f66])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.50  fof(f439,plain,(
% 0.22/0.50    spl3_23 | ~spl3_49),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f435])).
% 0.22/0.50  fof(f435,plain,(
% 0.22/0.50    $false | (spl3_23 | ~spl3_49)),
% 0.22/0.50    inference(resolution,[],[f425,f224])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_23),
% 0.22/0.50    inference(resolution,[],[f209,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~v1_relat_1(k2_funct_1(sK2)) | spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f426,plain,(
% 0.22/0.50    ~spl3_46 | spl3_49 | ~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_48),
% 0.22/0.50    inference(avatar_split_clause,[],[f421,f410,f303,f238,f156,f141,f424,f353])).
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    spl3_48 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.50  fof(f421,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f420,f239])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f419,f304])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_48)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f418])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_14 | ~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f417,f142])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_16 | ~spl3_30 | ~spl3_38 | ~spl3_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f416,f304])).
% 0.22/0.50  fof(f416,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_16 | ~spl3_30 | ~spl3_48)),
% 0.22/0.50    inference(forward_demodulation,[],[f413,f239])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_16 | ~spl3_48)),
% 0.22/0.50    inference(resolution,[],[f411,f157])).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_48),
% 0.22/0.50    inference(avatar_component_clause,[],[f410])).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    ~spl3_7 | spl3_48 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f408,f95,f410,f111])).
% 0.22/0.50  fof(f408,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f74,f96])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    ~spl3_35 | spl3_27 | ~spl3_16 | ~spl3_30 | ~spl3_40),
% 0.22/0.50    inference(avatar_split_clause,[],[f368,f312,f238,f156,f221,f265])).
% 0.22/0.50  fof(f265,plain,(
% 0.22/0.50    spl3_35 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.50  fof(f312,plain,(
% 0.22/0.50    spl3_40 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,k2_struct_0(sK0),X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.50  fof(f368,plain,(
% 0.22/0.50    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_16 | ~spl3_30 | ~spl3_40)),
% 0.22/0.50    inference(forward_demodulation,[],[f367,f239])).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | (~spl3_16 | ~spl3_30 | ~spl3_40)),
% 0.22/0.50    inference(forward_demodulation,[],[f365,f239])).
% 0.22/0.50  fof(f365,plain,(
% 0.22/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | (~spl3_16 | ~spl3_40)),
% 0.22/0.50    inference(resolution,[],[f313,f157])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),X0) | k1_xboole_0 = X0) ) | ~spl3_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f312])).
% 0.22/0.50  fof(f363,plain,(
% 0.22/0.50    spl3_46 | ~spl3_35 | ~spl3_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f338,f303,f265,f353])).
% 0.22/0.50  fof(f338,plain,(
% 0.22/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_35 | ~spl3_38)),
% 0.22/0.50    inference(superposition,[],[f266,f304])).
% 0.22/0.50  fof(f266,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f265])).
% 0.22/0.50  fof(f362,plain,(
% 0.22/0.50    spl3_45 | ~spl3_34 | ~spl3_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f337,f303,f261,f348])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    spl3_34 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_34 | ~spl3_38)),
% 0.22/0.50    inference(superposition,[],[f262,f304])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f261])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    ~spl3_7 | spl3_40 | spl3_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f310,f306,f312,f111])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    spl3_39 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.22/0.50  fof(f310,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),X0) | ~v1_funct_1(sK2)) ) | spl3_39),
% 0.22/0.50    inference(resolution,[],[f307,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f306])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    spl3_38 | ~spl3_39 | ~spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f300,f156,f306,f303])).
% 0.22/0.50  fof(f300,plain,(
% 0.22/0.50    ~v1_partfun1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_16),
% 0.22/0.50    inference(resolution,[],[f298,f157])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK2,X0) | k1_relat_1(sK2) = X0) ) | ~spl3_16),
% 0.22/0.50    inference(resolution,[],[f284,f157])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.22/0.50    inference(resolution,[],[f231,f65])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.22/0.50    inference(resolution,[],[f61,f63])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    k1_xboole_0 != k2_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f267,plain,(
% 0.22/0.50    spl3_35 | ~spl3_17 | ~spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f253,f238,f161,f265])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl3_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f253,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_17 | ~spl3_30)),
% 0.22/0.50    inference(superposition,[],[f162,f239])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    spl3_34 | ~spl3_16 | ~spl3_30),
% 0.22/0.50    inference(avatar_split_clause,[],[f252,f238,f156,f261])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_16 | ~spl3_30)),
% 0.22/0.50    inference(superposition,[],[f157,f239])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    spl3_30 | ~spl3_14 | ~spl3_29),
% 0.22/0.50    inference(avatar_split_clause,[],[f247,f234,f141,f238])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    spl3_29 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_14 | ~spl3_29)),
% 0.22/0.50    inference(superposition,[],[f142,f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f234])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl3_29 | ~spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f232,f156,f234])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_16),
% 0.22/0.50    inference(resolution,[],[f64,f157])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ~spl3_21 | ~spl3_7 | spl3_28 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f225,f95,f227,f111,f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    spl3_21 <=> v1_relat_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f60,f96])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    spl3_16 | ~spl3_5 | ~spl3_12 | ~spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f203,f137,f133,f103,f156])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl3_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl3_13 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_12 | ~spl3_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f202,f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f137])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_12)),
% 0.22/0.50    inference(forward_demodulation,[],[f104,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ~spl3_5 | spl3_21),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    $false | (~spl3_5 | spl3_21)),
% 0.22/0.50    inference(subsumption_resolution,[],[f104,f197])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_21),
% 0.22/0.50    inference(resolution,[],[f191,f63])).
% 0.22/0.50  fof(f191,plain,(
% 0.22/0.50    ~v1_relat_1(sK2) | spl3_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f190])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ~spl3_21 | ~spl3_7 | spl3_22 | ~spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f188,f95,f194,f111,f190])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.50    inference(resolution,[],[f59,f96])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    spl3_9 | ~spl3_8 | ~spl3_18 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f164,f133,f168,f115,f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl3_9 <=> v2_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl3_8 <=> l1_struct_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    spl3_18 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_12),
% 0.22/0.50    inference(superposition,[],[f58,f134])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl3_17 | ~spl3_6 | ~spl3_12 | ~spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f137,f133,f107,f161])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_12 | ~spl3_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f146,f138])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_12)),
% 0.22/0.50    inference(superposition,[],[f108,f134])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f107])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    spl3_14 | ~spl3_4 | ~spl3_12 | ~spl3_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f137,f133,f99,f141])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_12 | ~spl3_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f144,f138])).
% 0.22/0.50  fof(f144,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_12)),
% 0.22/0.50    inference(superposition,[],[f100,f134])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl3_13 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f131,f123,f137])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl3_10 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.22/0.50    inference(resolution,[],[f57,f124])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f123])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl3_12 | ~spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f130,f115,f133])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.22/0.50    inference(resolution,[],[f57,f116])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    l1_struct_0(sK1) | ~spl3_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f115])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl3_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f127])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    spl3_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f123])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    l1_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f40,f39,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f14])).
% 0.22/0.50  fof(f14,conjecture,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f46,f119])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ~v2_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f47,f115])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    l1_struct_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f48,f111])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    v1_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f49,f107])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  % (3640)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f103])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f99])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f95])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v2_funct_1(sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f91,f88])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (3630)------------------------------
% 0.22/0.50  % (3630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3630)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (3630)Memory used [KB]: 11001
% 0.22/0.50  % (3630)Time elapsed: 0.069 s
% 0.22/0.50  % (3630)------------------------------
% 0.22/0.50  % (3630)------------------------------
% 0.22/0.51  % (3624)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (3623)Success in time 0.145 s
%------------------------------------------------------------------------------
