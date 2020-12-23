%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:44 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  271 ( 539 expanded)
%              Number of leaves         :   67 ( 217 expanded)
%              Depth                    :   23
%              Number of atoms          : 1116 (2365 expanded)
%              Number of equality atoms :  212 ( 294 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f937,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f170,f196,f201,f224,f229,f251,f299,f306,f331,f377,f470,f478,f519,f647,f648,f649,f683,f692,f766,f771,f786,f791,f854,f857,f858,f860,f933,f936])).

fof(f936,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != sK1
    | k2_funct_1(k1_xboole_0) != k2_funct_2(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_funct_1(k1_xboole_0)
    | sK2 != k6_relat_1(sK0)
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f933,plain,
    ( spl3_84
    | ~ spl3_19
    | ~ spl3_68
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f932,f788,f768,f198,f917])).

fof(f917,plain,
    ( spl3_84
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f198,plain,
    ( spl3_19
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f768,plain,
    ( spl3_68
  <=> v5_relat_1(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f788,plain,
    ( spl3_72
  <=> v2_funct_2(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f932,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_19
    | ~ spl3_68
    | ~ spl3_72 ),
    inference(subsumption_resolution,[],[f931,f770])).

fof(f770,plain,
    ( v5_relat_1(sK1,k1_xboole_0)
    | ~ spl3_68 ),
    inference(avatar_component_clause,[],[f768])).

fof(f931,plain,
    ( k1_xboole_0 = sK1
    | ~ v5_relat_1(sK1,k1_xboole_0)
    | ~ spl3_19
    | ~ spl3_72 ),
    inference(subsumption_resolution,[],[f929,f200])).

fof(f200,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f929,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = sK1
    | ~ v5_relat_1(sK1,k1_xboole_0)
    | ~ spl3_72 ),
    inference(resolution,[],[f790,f450])).

fof(f450,plain,(
    ! [X0] :
      ( ~ v2_funct_2(X0,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v5_relat_1(X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f266])).

fof(f266,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 != X6
      | k1_xboole_0 = X5
      | ~ v1_relat_1(X5)
      | ~ v2_funct_2(X5,X6)
      | ~ v5_relat_1(X5,X6) ) ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,(
    ! [X6,X5] :
      ( k1_xboole_0 != X6
      | k1_xboole_0 = X5
      | ~ v1_relat_1(X5)
      | ~ v2_funct_2(X5,X6)
      | ~ v5_relat_1(X5,X6)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f83,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f83,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f790,plain,
    ( v2_funct_2(sK1,k1_xboole_0)
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f788])).

fof(f860,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != k6_relat_1(sK0)
    | k1_xboole_0 != sK0
    | k1_xboole_0 != sK2
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f858,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v3_funct_2(sK2,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f857,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK0
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK2,sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f854,plain,
    ( spl3_81
    | ~ spl3_18
    | ~ spl3_67
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f849,f783,f763,f193,f851])).

fof(f851,plain,
    ( spl3_81
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f193,plain,
    ( spl3_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f763,plain,
    ( spl3_67
  <=> v5_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).

fof(f783,plain,
    ( spl3_71
  <=> v2_funct_2(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f849,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_18
    | ~ spl3_67
    | ~ spl3_71 ),
    inference(subsumption_resolution,[],[f848,f765])).

fof(f765,plain,
    ( v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_67 ),
    inference(avatar_component_clause,[],[f763])).

fof(f848,plain,
    ( k1_xboole_0 = sK2
    | ~ v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_18
    | ~ spl3_71 ),
    inference(subsumption_resolution,[],[f846,f195])).

fof(f195,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f193])).

fof(f846,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_71 ),
    inference(resolution,[],[f785,f450])).

fof(f785,plain,
    ( v2_funct_2(sK2,k1_xboole_0)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f783])).

fof(f791,plain,
    ( spl3_72
    | ~ spl3_30
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f715,f644,f303,f788])).

fof(f303,plain,
    ( spl3_30
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f644,plain,
    ( spl3_53
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f715,plain,
    ( v2_funct_2(sK1,k1_xboole_0)
    | ~ spl3_30
    | ~ spl3_53 ),
    inference(backward_demodulation,[],[f305,f646])).

fof(f646,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f644])).

fof(f305,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f303])).

fof(f786,plain,
    ( spl3_71
    | ~ spl3_29
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f714,f644,f296,f783])).

fof(f296,plain,
    ( spl3_29
  <=> v2_funct_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f714,plain,
    ( v2_funct_2(sK2,k1_xboole_0)
    | ~ spl3_29
    | ~ spl3_53 ),
    inference(backward_demodulation,[],[f298,f646])).

fof(f298,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f296])).

fof(f771,plain,
    ( spl3_68
    | ~ spl3_22
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f711,f644,f226,f768])).

fof(f226,plain,
    ( spl3_22
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f711,plain,
    ( v5_relat_1(sK1,k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_53 ),
    inference(backward_demodulation,[],[f228,f646])).

fof(f228,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f226])).

fof(f766,plain,
    ( spl3_67
    | ~ spl3_21
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f710,f644,f221,f763])).

fof(f221,plain,
    ( spl3_21
  <=> v5_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f710,plain,
    ( v5_relat_1(sK2,k1_xboole_0)
    | ~ spl3_21
    | ~ spl3_53 ),
    inference(backward_demodulation,[],[f223,f646])).

fof(f223,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f221])).

fof(f692,plain,
    ( ~ spl3_41
    | ~ spl3_44
    | ~ spl3_42
    | spl3_45
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f488,f149,f434,f419,f430,f415])).

fof(f415,plain,
    ( spl3_41
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f430,plain,
    ( spl3_44
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f419,plain,
    ( spl3_42
  <=> v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f434,plain,
    ( spl3_45
  <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f149,plain,
    ( spl3_11
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f488,plain,
    ( k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)
    | ~ v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(superposition,[],[f315,f151])).

fof(f151,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f315,plain,(
    ! [X0] :
      ( k2_funct_2(X0,k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0))
      | ~ v3_funct_2(k6_relat_1(X0),X0,X0)
      | ~ v1_funct_2(k6_relat_1(X0),X0,X0)
      | ~ v1_funct_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f66,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_funct_2(X0,X1) = k2_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v3_funct_2(X1,X0,X0)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k2_funct_2(X0,X1) = k2_funct_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

fof(f683,plain,
    ( ~ spl3_41
    | spl3_58
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f533,f149,f679,f415])).

fof(f679,plain,
    ( spl3_58
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f533,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_11 ),
    inference(superposition,[],[f500,f151])).

fof(f500,plain,(
    ! [X1] :
      ( k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1)) ) ),
    inference(trivial_inequality_removal,[],[f499])).

fof(f499,plain,(
    ! [X1] :
      ( k6_relat_1(X1) != k6_relat_1(X1)
      | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f498,f84])).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f498,plain,(
    ! [X1] :
      ( k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1)))
      | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f497,f87])).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f497,plain,(
    ! [X1] :
      ( k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1)))
      | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f494,f85])).

fof(f85,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f494,plain,(
    ! [X1] :
      ( k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1)))
      | k2_relat_1(k6_relat_1(X1)) != X1
      | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f491])).

fof(f491,plain,(
    ! [X1] :
      ( k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1)))
      | k2_relat_1(k6_relat_1(X1)) != X1
      | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f336,f204])).

fof(f204,plain,(
    ! [X0] : k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f202,f87])).

fof(f202,plain,(
    ! [X0] :
      ( k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f93,f85])).

fof(f93,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f336,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0)
      | k2_relat_1(X0) != X1
      | k2_funct_1(X0) = k6_relat_1(X1)
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f335,f84])).

fof(f335,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0)
      | k2_funct_1(X0) = k6_relat_1(X1)
      | k2_relat_1(X0) != k1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f334,f87])).

fof(f334,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0)
      | k2_funct_1(X0) = k6_relat_1(X1)
      | k2_relat_1(X0) != k1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f333])).

fof(f333,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0)
      | k2_funct_1(X0) = k6_relat_1(X1)
      | k2_relat_1(X0) != k1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f332,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f332,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f80,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f649,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k6_relat_1(k1_xboole_0)
    | v1_funct_1(k1_xboole_0)
    | ~ v1_funct_1(k6_relat_1(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f648,plain,
    ( sK2 != k2_funct_1(sK1)
    | k2_funct_2(sK0,sK1) != k2_funct_1(sK1)
    | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    | ~ r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f647,plain,
    ( spl3_52
    | spl3_53
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f638,f467,f303,f144,f139,f129,f124,f119,f109,f644,f640])).

fof(f640,plain,
    ( spl3_52
  <=> sK2 = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f109,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f119,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f124,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f129,plain,
    ( spl3_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f139,plain,
    ( spl3_9
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f144,plain,
    ( spl3_10
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f467,plain,
    ( spl3_47
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f638,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f637,f305])).

fof(f637,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f636,f146])).

fof(f146,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f144])).

fof(f636,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f635,f141])).

fof(f141,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f139])).

fof(f635,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f634,f131])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f634,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f633,f126])).

fof(f126,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f633,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f632,f121])).

fof(f121,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f632,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f631,f111])).

fof(f111,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f631,plain,
    ( k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f630,f246])).

fof(f246,plain,(
    ! [X0] : r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0)) ),
    inference(resolution,[],[f97,f79])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f630,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_47 ),
    inference(duplicate_literal_removal,[],[f627])).

fof(f627,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | sK2 = k2_funct_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | ~ spl3_47 ),
    inference(superposition,[],[f607,f469])).

fof(f469,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f467])).

fof(f607,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_relset_1(X7,X7,k1_partfun1(X7,X6,X6,X7,X5,X8),k6_relat_1(X7))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k2_funct_1(X5) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_2(X8,X6,X7)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ v1_funct_2(X5,X7,X6)
      | ~ v1_funct_1(X5)
      | ~ v2_funct_2(X5,X6) ) ),
    inference(subsumption_resolution,[],[f606,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f606,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_relset_1(X7,X7,k1_partfun1(X7,X6,X6,X7,X5,X8),k6_relat_1(X7))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k2_funct_1(X5) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_2(X8,X6,X7)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ v1_funct_2(X5,X7,X6)
      | ~ v1_funct_1(X5)
      | ~ v2_funct_2(X5,X6)
      | ~ v1_relat_1(X5) ) ),
    inference(subsumption_resolution,[],[f603,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f603,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_relset_1(X7,X7,k1_partfun1(X7,X6,X6,X7,X5,X8),k6_relat_1(X7))
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | k2_funct_1(X5) = X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_2(X8,X6,X7)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ v1_funct_2(X5,X7,X6)
      | ~ v1_funct_1(X5)
      | ~ v2_funct_2(X5,X6)
      | ~ v5_relat_1(X5,X6)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f531,f90])).

fof(f531,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_relset_1(X2,X2,k1_partfun1(X2,k2_relat_1(X0),k2_relat_1(X0),X2,X0,X1),k6_relat_1(X2))
      | k2_relat_1(X0) = k1_xboole_0
      | k1_xboole_0 = X2
      | k2_funct_1(X0) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X2)))
      | ~ v1_funct_2(X1,k2_relat_1(X0),X2)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X0))))
      | ~ v1_funct_2(X0,X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0) ) ),
    inference(equality_resolution,[],[f384])).

fof(f384,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f383])).

fof(f383,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relat_1(X2) != X1
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f382,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f382,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(subsumption_resolution,[],[f381,f353])).

fof(f353,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | v2_funct_1(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f70,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f381,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0))
      | k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f69,f72])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_funct_1(X2) = X3
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ v2_funct_1(X2)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_funct_1(X2) = X3
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | ~ v2_funct_1(X2)
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | k2_relset_1(X0,X1,X2) != X1
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f519,plain,
    ( spl3_48
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f514,f467,f144,f129,f124,f109,f516])).

fof(f516,plain,
    ( spl3_48
  <=> v1_funct_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f514,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f513,f146])).

fof(f513,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f512,f131])).

fof(f512,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f511,f126])).

fof(f511,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f508,f111])).

fof(f508,plain,
    ( v1_funct_1(k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_47 ),
    inference(superposition,[],[f73,f469])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f478,plain,
    ( ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | spl3_46 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_10
    | spl3_46 ),
    inference(subsumption_resolution,[],[f476,f146])).

fof(f476,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_7
    | spl3_46 ),
    inference(subsumption_resolution,[],[f475,f131])).

fof(f475,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | ~ spl3_6
    | spl3_46 ),
    inference(subsumption_resolution,[],[f474,f126])).

fof(f474,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl3_3
    | spl3_46 ),
    inference(subsumption_resolution,[],[f472,f111])).

fof(f472,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | spl3_46 ),
    inference(resolution,[],[f465,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f465,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f463])).

fof(f463,plain,
    ( spl3_46
  <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f470,plain,
    ( ~ spl3_46
    | spl3_47
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f459,f167,f467,f463])).

fof(f167,plain,
    ( spl3_14
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f459,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl3_14 ),
    inference(resolution,[],[f312,f169])).

fof(f169,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f312,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f67,f79])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f377,plain,
    ( ~ spl3_36
    | spl3_37
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f358,f109,f374,f370])).

fof(f370,plain,
    ( spl3_36
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f374,plain,
    ( spl3_37
  <=> sK2 = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f358,plain,
    ( sK2 = k6_relat_1(sK0)
    | ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f310,f79])).

fof(f310,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK2 = X0
        | ~ r2_relset_1(sK0,sK0,X0,sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f67,f111])).

fof(f331,plain,
    ( spl3_32
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f326,f144,f139,f134,f129,f328])).

fof(f328,plain,
    ( spl3_32
  <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f134,plain,
    ( spl3_8
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f326,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f325,f146])).

fof(f325,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f324,f141])).

fof(f324,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f314,f136])).

fof(f136,plain,
    ( v3_funct_2(sK1,sK0,sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f134])).

fof(f314,plain,
    ( k2_funct_2(sK0,sK1) = k2_funct_1(sK1)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f66,f131])).

fof(f306,plain,
    ( spl3_30
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f301,f144,f134,f129,f303])).

fof(f301,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f300,f146])).

fof(f300,plain,
    ( ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f291,f136])).

fof(f291,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f77,f131])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f299,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f294,f124,f114,f109,f296])).

fof(f114,plain,
    ( spl3_4
  <=> v3_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f294,plain,
    ( v2_funct_2(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f293,f126])).

fof(f293,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f290,f116])).

fof(f116,plain,
    ( v3_funct_2(sK2,sK0,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f290,plain,
    ( ~ v3_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f77,f111])).

fof(f251,plain,
    ( spl3_25
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f244,f109,f248])).

fof(f248,plain,
    ( spl3_25
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f244,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f97,f111])).

fof(f229,plain,
    ( spl3_22
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f218,f129,f226])).

fof(f218,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f94,f131])).

fof(f224,plain,
    ( spl3_21
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f217,f109,f221])).

fof(f217,plain,
    ( v5_relat_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f94,f111])).

fof(f201,plain,
    ( spl3_19
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f190,f129,f198])).

fof(f190,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f78,f131])).

fof(f196,plain,
    ( spl3_18
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f189,f109,f193])).

fof(f189,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f78,f111])).

fof(f170,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f165,f104,f167])).

fof(f104,plain,
    ( spl3_2
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f165,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f106,f72])).

fof(f106,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f152,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f86,f149])).

fof(f86,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f147,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f56,f144])).

fof(f56,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK2,sK0,sK0)
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v3_funct_2(sK1,sK0,sK0)
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f52,f51])).

fof(f51,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v3_funct_2(X2,sK0,sK0)
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK1,sK0,sK0)
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1))
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v3_funct_2(X2,sK0,sK0)
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v3_funct_2(sK2,sK0,sK0)
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1))
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X1,X0,X0)
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v3_funct_2(X2,X0,X0)
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
             => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X1,X0,X0)
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X2,X0,X0)
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))
           => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).

fof(f142,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f57,f139])).

fof(f57,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f137,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f58,f134])).

fof(f58,plain,(
    v3_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f132,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f59,f129])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f127,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f60,f124])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f122,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f61,f119])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f62,f114])).

fof(f62,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f112,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f63,f109])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f107,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f64,f104])).

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f65,f99])).

fof(f99,plain,
    ( spl3_1
  <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (14301)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.49  % (14316)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (14322)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (14302)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (14304)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (14303)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (14309)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (14313)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (14327)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (14311)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (14329)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (14305)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (14323)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (14314)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (14320)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (14325)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (14328)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (14317)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (14306)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (14315)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.54  % (14317)Refutation not found, incomplete strategy% (14317)------------------------------
% 0.20/0.54  % (14317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (14317)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (14317)Memory used [KB]: 10746
% 0.20/0.54  % (14317)Time elapsed: 0.144 s
% 0.20/0.54  % (14317)------------------------------
% 0.20/0.54  % (14317)------------------------------
% 0.20/0.54  % (14330)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (14311)Refutation not found, incomplete strategy% (14311)------------------------------
% 0.20/0.54  % (14311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (14321)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.55  % (14310)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (14319)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (14324)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.55  % (14312)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.55  % (14325)Refutation not found, incomplete strategy% (14325)------------------------------
% 1.41/0.55  % (14325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (14311)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  % (14325)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (14325)Memory used [KB]: 10746
% 1.41/0.55  % (14325)Time elapsed: 0.137 s
% 1.41/0.55  % (14325)------------------------------
% 1.41/0.55  % (14325)------------------------------
% 1.41/0.55  
% 1.41/0.55  % (14311)Memory used [KB]: 11129
% 1.41/0.55  % (14311)Time elapsed: 0.123 s
% 1.41/0.55  % (14311)------------------------------
% 1.41/0.55  % (14311)------------------------------
% 1.41/0.55  % (14307)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.56  % (14318)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.56  % (14328)Refutation not found, incomplete strategy% (14328)------------------------------
% 1.41/0.56  % (14328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (14308)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.57/0.57  % (14328)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (14328)Memory used [KB]: 6268
% 1.57/0.57  % (14328)Time elapsed: 0.152 s
% 1.57/0.57  % (14328)------------------------------
% 1.57/0.57  % (14328)------------------------------
% 1.57/0.57  % (14326)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.57  % (14329)Refutation not found, incomplete strategy% (14329)------------------------------
% 1.57/0.57  % (14329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (14329)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (14329)Memory used [KB]: 11129
% 1.57/0.57  % (14329)Time elapsed: 0.156 s
% 1.57/0.57  % (14329)------------------------------
% 1.57/0.57  % (14329)------------------------------
% 1.57/0.58  % (14322)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.60  fof(f937,plain,(
% 1.57/0.60    $false),
% 1.57/0.60    inference(avatar_sat_refutation,[],[f102,f107,f112,f117,f122,f127,f132,f137,f142,f147,f152,f170,f196,f201,f224,f229,f251,f299,f306,f331,f377,f470,f478,f519,f647,f648,f649,f683,f692,f766,f771,f786,f791,f854,f857,f858,f860,f933,f936])).
% 1.57/0.60  fof(f936,plain,(
% 1.57/0.60    k1_xboole_0 != sK0 | k1_xboole_0 != sK1 | k2_funct_1(k1_xboole_0) != k2_funct_2(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_funct_1(k1_xboole_0) | sK2 != k6_relat_1(sK0) | k1_xboole_0 != k6_relat_1(k1_xboole_0) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f933,plain,(
% 1.57/0.60    spl3_84 | ~spl3_19 | ~spl3_68 | ~spl3_72),
% 1.57/0.60    inference(avatar_split_clause,[],[f932,f788,f768,f198,f917])).
% 1.57/0.60  fof(f917,plain,(
% 1.57/0.60    spl3_84 <=> k1_xboole_0 = sK1),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 1.57/0.60  fof(f198,plain,(
% 1.57/0.60    spl3_19 <=> v1_relat_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.57/0.60  fof(f768,plain,(
% 1.57/0.60    spl3_68 <=> v5_relat_1(sK1,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 1.57/0.60  fof(f788,plain,(
% 1.57/0.60    spl3_72 <=> v2_funct_2(sK1,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 1.57/0.60  fof(f932,plain,(
% 1.57/0.60    k1_xboole_0 = sK1 | (~spl3_19 | ~spl3_68 | ~spl3_72)),
% 1.57/0.60    inference(subsumption_resolution,[],[f931,f770])).
% 1.57/0.60  fof(f770,plain,(
% 1.57/0.60    v5_relat_1(sK1,k1_xboole_0) | ~spl3_68),
% 1.57/0.60    inference(avatar_component_clause,[],[f768])).
% 1.57/0.60  fof(f931,plain,(
% 1.57/0.60    k1_xboole_0 = sK1 | ~v5_relat_1(sK1,k1_xboole_0) | (~spl3_19 | ~spl3_72)),
% 1.57/0.60    inference(subsumption_resolution,[],[f929,f200])).
% 1.57/0.60  fof(f200,plain,(
% 1.57/0.60    v1_relat_1(sK1) | ~spl3_19),
% 1.57/0.60    inference(avatar_component_clause,[],[f198])).
% 1.57/0.60  fof(f929,plain,(
% 1.57/0.60    ~v1_relat_1(sK1) | k1_xboole_0 = sK1 | ~v5_relat_1(sK1,k1_xboole_0) | ~spl3_72),
% 1.57/0.60    inference(resolution,[],[f790,f450])).
% 1.57/0.60  fof(f450,plain,(
% 1.57/0.60    ( ! [X0] : (~v2_funct_2(X0,k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = X0 | ~v5_relat_1(X0,k1_xboole_0)) )),
% 1.57/0.60    inference(equality_resolution,[],[f266])).
% 1.57/0.60  fof(f266,plain,(
% 1.57/0.60    ( ! [X6,X5] : (k1_xboole_0 != X6 | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v2_funct_2(X5,X6) | ~v5_relat_1(X5,X6)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f263])).
% 1.57/0.60  fof(f263,plain,(
% 1.57/0.60    ( ! [X6,X5] : (k1_xboole_0 != X6 | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v2_funct_2(X5,X6) | ~v5_relat_1(X5,X6) | ~v1_relat_1(X5)) )),
% 1.57/0.60    inference(superposition,[],[f83,f90])).
% 1.57/0.60  fof(f90,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f55])).
% 1.57/0.60  fof(f55,plain,(
% 1.57/0.60    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(nnf_transformation,[],[f47])).
% 1.57/0.60  fof(f47,plain,(
% 1.57/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(flattening,[],[f46])).
% 1.57/0.60  fof(f46,plain,(
% 1.57/0.60    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f15])).
% 1.57/0.60  fof(f15,axiom,(
% 1.57/0.60    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.57/0.60  fof(f83,plain,(
% 1.57/0.60    ( ! [X0] : (k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f44])).
% 1.57/0.60  fof(f44,plain,(
% 1.57/0.60    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(flattening,[],[f43])).
% 1.57/0.60  fof(f43,plain,(
% 1.57/0.60    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f3])).
% 1.57/0.60  fof(f3,axiom,(
% 1.57/0.60    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.57/0.60  fof(f790,plain,(
% 1.57/0.60    v2_funct_2(sK1,k1_xboole_0) | ~spl3_72),
% 1.57/0.60    inference(avatar_component_clause,[],[f788])).
% 1.57/0.60  fof(f860,plain,(
% 1.57/0.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) != k6_relat_1(sK0) | k1_xboole_0 != sK0 | k1_xboole_0 != sK2 | k1_xboole_0 != k6_relat_1(k1_xboole_0) | r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f858,plain,(
% 1.57/0.60    k1_xboole_0 != sK2 | k1_xboole_0 != k6_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v3_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f857,plain,(
% 1.57/0.60    k1_xboole_0 != sK2 | k1_xboole_0 != k6_relat_1(k1_xboole_0) | k1_xboole_0 != sK0 | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f854,plain,(
% 1.57/0.60    spl3_81 | ~spl3_18 | ~spl3_67 | ~spl3_71),
% 1.57/0.60    inference(avatar_split_clause,[],[f849,f783,f763,f193,f851])).
% 1.57/0.60  fof(f851,plain,(
% 1.57/0.60    spl3_81 <=> k1_xboole_0 = sK2),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 1.57/0.60  fof(f193,plain,(
% 1.57/0.60    spl3_18 <=> v1_relat_1(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.57/0.60  fof(f763,plain,(
% 1.57/0.60    spl3_67 <=> v5_relat_1(sK2,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_67])])).
% 1.57/0.60  fof(f783,plain,(
% 1.57/0.60    spl3_71 <=> v2_funct_2(sK2,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 1.57/0.60  fof(f849,plain,(
% 1.57/0.60    k1_xboole_0 = sK2 | (~spl3_18 | ~spl3_67 | ~spl3_71)),
% 1.57/0.60    inference(subsumption_resolution,[],[f848,f765])).
% 1.57/0.60  fof(f765,plain,(
% 1.57/0.60    v5_relat_1(sK2,k1_xboole_0) | ~spl3_67),
% 1.57/0.60    inference(avatar_component_clause,[],[f763])).
% 1.57/0.60  fof(f848,plain,(
% 1.57/0.60    k1_xboole_0 = sK2 | ~v5_relat_1(sK2,k1_xboole_0) | (~spl3_18 | ~spl3_71)),
% 1.57/0.60    inference(subsumption_resolution,[],[f846,f195])).
% 1.57/0.60  fof(f195,plain,(
% 1.57/0.60    v1_relat_1(sK2) | ~spl3_18),
% 1.57/0.60    inference(avatar_component_clause,[],[f193])).
% 1.57/0.60  fof(f846,plain,(
% 1.57/0.60    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~v5_relat_1(sK2,k1_xboole_0) | ~spl3_71),
% 1.57/0.60    inference(resolution,[],[f785,f450])).
% 1.57/0.60  fof(f785,plain,(
% 1.57/0.60    v2_funct_2(sK2,k1_xboole_0) | ~spl3_71),
% 1.57/0.60    inference(avatar_component_clause,[],[f783])).
% 1.57/0.60  fof(f791,plain,(
% 1.57/0.60    spl3_72 | ~spl3_30 | ~spl3_53),
% 1.57/0.60    inference(avatar_split_clause,[],[f715,f644,f303,f788])).
% 1.57/0.60  fof(f303,plain,(
% 1.57/0.60    spl3_30 <=> v2_funct_2(sK1,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.57/0.60  fof(f644,plain,(
% 1.57/0.60    spl3_53 <=> k1_xboole_0 = sK0),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 1.57/0.60  fof(f715,plain,(
% 1.57/0.60    v2_funct_2(sK1,k1_xboole_0) | (~spl3_30 | ~spl3_53)),
% 1.57/0.60    inference(backward_demodulation,[],[f305,f646])).
% 1.57/0.60  fof(f646,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | ~spl3_53),
% 1.57/0.60    inference(avatar_component_clause,[],[f644])).
% 1.57/0.60  fof(f305,plain,(
% 1.57/0.60    v2_funct_2(sK1,sK0) | ~spl3_30),
% 1.57/0.60    inference(avatar_component_clause,[],[f303])).
% 1.57/0.60  fof(f786,plain,(
% 1.57/0.60    spl3_71 | ~spl3_29 | ~spl3_53),
% 1.57/0.60    inference(avatar_split_clause,[],[f714,f644,f296,f783])).
% 1.57/0.60  fof(f296,plain,(
% 1.57/0.60    spl3_29 <=> v2_funct_2(sK2,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.57/0.60  fof(f714,plain,(
% 1.57/0.60    v2_funct_2(sK2,k1_xboole_0) | (~spl3_29 | ~spl3_53)),
% 1.57/0.60    inference(backward_demodulation,[],[f298,f646])).
% 1.57/0.60  fof(f298,plain,(
% 1.57/0.60    v2_funct_2(sK2,sK0) | ~spl3_29),
% 1.57/0.60    inference(avatar_component_clause,[],[f296])).
% 1.57/0.60  fof(f771,plain,(
% 1.57/0.60    spl3_68 | ~spl3_22 | ~spl3_53),
% 1.57/0.60    inference(avatar_split_clause,[],[f711,f644,f226,f768])).
% 1.57/0.60  fof(f226,plain,(
% 1.57/0.60    spl3_22 <=> v5_relat_1(sK1,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.57/0.60  fof(f711,plain,(
% 1.57/0.60    v5_relat_1(sK1,k1_xboole_0) | (~spl3_22 | ~spl3_53)),
% 1.57/0.60    inference(backward_demodulation,[],[f228,f646])).
% 1.57/0.60  fof(f228,plain,(
% 1.57/0.60    v5_relat_1(sK1,sK0) | ~spl3_22),
% 1.57/0.60    inference(avatar_component_clause,[],[f226])).
% 1.57/0.60  fof(f766,plain,(
% 1.57/0.60    spl3_67 | ~spl3_21 | ~spl3_53),
% 1.57/0.60    inference(avatar_split_clause,[],[f710,f644,f221,f763])).
% 1.57/0.60  fof(f221,plain,(
% 1.57/0.60    spl3_21 <=> v5_relat_1(sK2,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.57/0.60  fof(f710,plain,(
% 1.57/0.60    v5_relat_1(sK2,k1_xboole_0) | (~spl3_21 | ~spl3_53)),
% 1.57/0.60    inference(backward_demodulation,[],[f223,f646])).
% 1.57/0.60  fof(f223,plain,(
% 1.57/0.60    v5_relat_1(sK2,sK0) | ~spl3_21),
% 1.57/0.60    inference(avatar_component_clause,[],[f221])).
% 1.57/0.60  fof(f692,plain,(
% 1.57/0.60    ~spl3_41 | ~spl3_44 | ~spl3_42 | spl3_45 | ~spl3_11),
% 1.57/0.60    inference(avatar_split_clause,[],[f488,f149,f434,f419,f430,f415])).
% 1.57/0.60  fof(f415,plain,(
% 1.57/0.60    spl3_41 <=> v1_funct_1(k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.57/0.60  fof(f430,plain,(
% 1.57/0.60    spl3_44 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.57/0.60  fof(f419,plain,(
% 1.57/0.60    spl3_42 <=> v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.57/0.60  fof(f434,plain,(
% 1.57/0.60    spl3_45 <=> k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.57/0.60  fof(f149,plain,(
% 1.57/0.60    spl3_11 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.57/0.60  fof(f488,plain,(
% 1.57/0.60    k2_funct_1(k1_xboole_0) = k2_funct_2(k1_xboole_0,k1_xboole_0) | ~v3_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~spl3_11),
% 1.57/0.60    inference(superposition,[],[f315,f151])).
% 1.57/0.60  fof(f151,plain,(
% 1.57/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl3_11),
% 1.57/0.60    inference(avatar_component_clause,[],[f149])).
% 1.57/0.60  fof(f315,plain,(
% 1.57/0.60    ( ! [X0] : (k2_funct_2(X0,k6_relat_1(X0)) = k2_funct_1(k6_relat_1(X0)) | ~v3_funct_2(k6_relat_1(X0),X0,X0) | ~v1_funct_2(k6_relat_1(X0),X0,X0) | ~v1_funct_1(k6_relat_1(X0))) )),
% 1.57/0.60    inference(resolution,[],[f66,f79])).
% 1.57/0.60  fof(f79,plain,(
% 1.57/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f13])).
% 1.57/0.60  fof(f13,axiom,(
% 1.57/0.60    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.57/0.60  fof(f66,plain,(
% 1.57/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k2_funct_2(X0,X1) = k2_funct_1(X1) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f27])).
% 1.57/0.60  fof(f27,plain,(
% 1.57/0.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 1.57/0.60    inference(flattening,[],[f26])).
% 1.57/0.60  fof(f26,plain,(
% 1.57/0.60    ! [X0,X1] : (k2_funct_2(X0,X1) = k2_funct_1(X1) | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f17])).
% 1.57/0.60  fof(f17,axiom,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k2_funct_2(X0,X1) = k2_funct_1(X1))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).
% 1.57/0.60  fof(f683,plain,(
% 1.57/0.60    ~spl3_41 | spl3_58 | ~spl3_11),
% 1.57/0.60    inference(avatar_split_clause,[],[f533,f149,f679,f415])).
% 1.57/0.60  fof(f679,plain,(
% 1.57/0.60    spl3_58 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.57/0.60  fof(f533,plain,(
% 1.57/0.60    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~spl3_11),
% 1.57/0.60    inference(superposition,[],[f500,f151])).
% 1.57/0.60  fof(f500,plain,(
% 1.57/0.60    ( ! [X1] : (k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1))) )),
% 1.57/0.60    inference(trivial_inequality_removal,[],[f499])).
% 1.57/0.60  fof(f499,plain,(
% 1.57/0.60    ( ! [X1] : (k6_relat_1(X1) != k6_relat_1(X1) | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1))) )),
% 1.57/0.60    inference(forward_demodulation,[],[f498,f84])).
% 1.57/0.60  fof(f84,plain,(
% 1.57/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f4])).
% 1.57/0.60  fof(f4,axiom,(
% 1.57/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.57/0.60  fof(f498,plain,(
% 1.57/0.60    ( ! [X1] : (k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1))) | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f497,f87])).
% 1.57/0.60  fof(f87,plain,(
% 1.57/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f6])).
% 1.57/0.60  fof(f6,axiom,(
% 1.57/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.57/0.60  fof(f497,plain,(
% 1.57/0.60    ( ! [X1] : (k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1))) | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f494,f85])).
% 1.57/0.60  fof(f85,plain,(
% 1.57/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.57/0.60    inference(cnf_transformation,[],[f4])).
% 1.57/0.60  fof(f494,plain,(
% 1.57/0.60    ( ! [X1] : (k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1))) | k2_relat_1(k6_relat_1(X1)) != X1 | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f491])).
% 1.57/0.60  fof(f491,plain,(
% 1.57/0.60    ( ! [X1] : (k6_relat_1(X1) != k6_relat_1(k1_relat_1(k6_relat_1(X1))) | k2_relat_1(k6_relat_1(X1)) != X1 | k6_relat_1(X1) = k2_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.57/0.60    inference(superposition,[],[f336,f204])).
% 1.57/0.60  fof(f204,plain,(
% 1.57/0.60    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0))) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f202,f87])).
% 1.57/0.60  fof(f202,plain,(
% 1.57/0.60    ( ! [X0] : (k6_relat_1(X0) = k8_relat_1(X0,k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.57/0.60    inference(superposition,[],[f93,f85])).
% 1.57/0.60  fof(f93,plain,(
% 1.57/0.60    ( ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f49])).
% 1.57/0.60  fof(f49,plain,(
% 1.57/0.60    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 1.57/0.60    inference(ennf_transformation,[],[f2])).
% 1.57/0.60  fof(f2,axiom,(
% 1.57/0.60    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).
% 1.57/0.60  fof(f336,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0) | k2_relat_1(X0) != X1 | k2_funct_1(X0) = k6_relat_1(X1) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f335,f84])).
% 1.57/0.60  fof(f335,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0) | k2_funct_1(X0) = k6_relat_1(X1) | k2_relat_1(X0) != k1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f334,f87])).
% 1.57/0.60  fof(f334,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0) | k2_funct_1(X0) = k6_relat_1(X1) | k2_relat_1(X0) != k1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f333])).
% 1.57/0.60  fof(f333,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X0)) != k8_relat_1(X1,X0) | k2_funct_1(X0) = k6_relat_1(X1) | k2_relat_1(X0) != k1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(superposition,[],[f332,f92])).
% 1.57/0.60  fof(f92,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f48])).
% 1.57/0.60  fof(f48,plain,(
% 1.57/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.57/0.60    inference(ennf_transformation,[],[f1])).
% 1.57/0.60  fof(f1,axiom,(
% 1.57/0.60    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 1.57/0.60  fof(f332,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f80,f81])).
% 1.57/0.60  fof(f81,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f42])).
% 1.57/0.60  fof(f42,plain,(
% 1.57/0.60    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(flattening,[],[f41])).
% 1.57/0.60  fof(f41,plain,(
% 1.57/0.60    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f7])).
% 1.57/0.60  fof(f7,axiom,(
% 1.57/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 1.57/0.60  fof(f80,plain,(
% 1.57/0.60    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f40])).
% 1.57/0.60  fof(f40,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.57/0.60    inference(flattening,[],[f39])).
% 1.57/0.60  fof(f39,plain,(
% 1.57/0.60    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.57/0.60    inference(ennf_transformation,[],[f8])).
% 1.57/0.60  fof(f8,axiom,(
% 1.57/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 1.57/0.60  fof(f649,plain,(
% 1.57/0.60    k1_xboole_0 != sK0 | k1_xboole_0 != k6_relat_1(k1_xboole_0) | v1_funct_1(k1_xboole_0) | ~v1_funct_1(k6_relat_1(sK0))),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f648,plain,(
% 1.57/0.60    sK2 != k2_funct_1(sK1) | k2_funct_2(sK0,sK1) != k2_funct_1(sK1) | r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) | ~r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.57/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.57/0.60  fof(f647,plain,(
% 1.57/0.60    spl3_52 | spl3_53 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_30 | ~spl3_47),
% 1.57/0.60    inference(avatar_split_clause,[],[f638,f467,f303,f144,f139,f129,f124,f119,f109,f644,f640])).
% 1.57/0.60  fof(f640,plain,(
% 1.57/0.60    spl3_52 <=> sK2 = k2_funct_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.57/0.60  fof(f109,plain,(
% 1.57/0.60    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.57/0.60  fof(f119,plain,(
% 1.57/0.60    spl3_5 <=> v1_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.57/0.60  fof(f124,plain,(
% 1.57/0.60    spl3_6 <=> v1_funct_1(sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.57/0.60  fof(f129,plain,(
% 1.57/0.60    spl3_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.57/0.60  fof(f139,plain,(
% 1.57/0.60    spl3_9 <=> v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.57/0.60  fof(f144,plain,(
% 1.57/0.60    spl3_10 <=> v1_funct_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.57/0.60  fof(f467,plain,(
% 1.57/0.60    spl3_47 <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 1.57/0.60  fof(f638,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_30 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f637,f305])).
% 1.57/0.60  fof(f637,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f636,f146])).
% 1.57/0.60  fof(f146,plain,(
% 1.57/0.60    v1_funct_1(sK1) | ~spl3_10),
% 1.57/0.60    inference(avatar_component_clause,[],[f144])).
% 1.57/0.60  fof(f636,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_9 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f635,f141])).
% 1.57/0.60  fof(f141,plain,(
% 1.57/0.60    v1_funct_2(sK1,sK0,sK0) | ~spl3_9),
% 1.57/0.60    inference(avatar_component_clause,[],[f139])).
% 1.57/0.60  fof(f635,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_7 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f634,f131])).
% 1.57/0.60  fof(f131,plain,(
% 1.57/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_7),
% 1.57/0.60    inference(avatar_component_clause,[],[f129])).
% 1.57/0.60  fof(f634,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f633,f126])).
% 1.57/0.60  fof(f126,plain,(
% 1.57/0.60    v1_funct_1(sK2) | ~spl3_6),
% 1.57/0.60    inference(avatar_component_clause,[],[f124])).
% 1.57/0.60  fof(f633,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_5 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f632,f121])).
% 1.57/0.60  fof(f121,plain,(
% 1.57/0.60    v1_funct_2(sK2,sK0,sK0) | ~spl3_5),
% 1.57/0.60    inference(avatar_component_clause,[],[f119])).
% 1.57/0.60  fof(f632,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | (~spl3_3 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f631,f111])).
% 1.57/0.60  fof(f111,plain,(
% 1.57/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_3),
% 1.57/0.60    inference(avatar_component_clause,[],[f109])).
% 1.57/0.60  fof(f631,plain,(
% 1.57/0.60    k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | ~spl3_47),
% 1.57/0.60    inference(subsumption_resolution,[],[f630,f246])).
% 1.57/0.60  fof(f246,plain,(
% 1.57/0.60    ( ! [X0] : (r2_relset_1(X0,X0,k6_relat_1(X0),k6_relat_1(X0))) )),
% 1.57/0.60    inference(resolution,[],[f97,f79])).
% 1.57/0.60  fof(f97,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f95])).
% 1.57/0.60  fof(f95,plain,(
% 1.57/0.60    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(equality_resolution,[],[f68])).
% 1.57/0.60  fof(f68,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f54])).
% 1.57/0.60  fof(f54,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(nnf_transformation,[],[f29])).
% 1.57/0.60  fof(f29,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(flattening,[],[f28])).
% 1.57/0.60  fof(f28,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.57/0.60    inference(ennf_transformation,[],[f12])).
% 1.57/0.60  fof(f12,axiom,(
% 1.57/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.57/0.60  fof(f630,plain,(
% 1.57/0.60    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | ~spl3_47),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f627])).
% 1.57/0.60  fof(f627,plain,(
% 1.57/0.60    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | sK2 = k2_funct_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | ~spl3_47),
% 1.57/0.60    inference(superposition,[],[f607,f469])).
% 1.57/0.60  fof(f469,plain,(
% 1.57/0.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~spl3_47),
% 1.57/0.60    inference(avatar_component_clause,[],[f467])).
% 1.57/0.60  fof(f607,plain,(
% 1.57/0.60    ( ! [X6,X8,X7,X5] : (~r2_relset_1(X7,X7,k1_partfun1(X7,X6,X6,X7,X5,X8),k6_relat_1(X7)) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k2_funct_1(X5) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X8,X6,X7) | ~v1_funct_1(X8) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~v1_funct_2(X5,X7,X6) | ~v1_funct_1(X5) | ~v2_funct_2(X5,X6)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f606,f78])).
% 1.57/0.60  fof(f78,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f38])).
% 1.57/0.60  fof(f38,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f9])).
% 1.57/0.60  fof(f9,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.57/0.60  fof(f606,plain,(
% 1.57/0.60    ( ! [X6,X8,X7,X5] : (~r2_relset_1(X7,X7,k1_partfun1(X7,X6,X6,X7,X5,X8),k6_relat_1(X7)) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k2_funct_1(X5) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X8,X6,X7) | ~v1_funct_1(X8) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~v1_funct_2(X5,X7,X6) | ~v1_funct_1(X5) | ~v2_funct_2(X5,X6) | ~v1_relat_1(X5)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f603,f94])).
% 1.57/0.60  fof(f94,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f50])).
% 1.57/0.60  fof(f50,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f23])).
% 1.57/0.60  fof(f23,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.57/0.60    inference(pure_predicate_removal,[],[f10])).
% 1.57/0.60  fof(f10,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.57/0.60  fof(f603,plain,(
% 1.57/0.60    ( ! [X6,X8,X7,X5] : (~r2_relset_1(X7,X7,k1_partfun1(X7,X6,X6,X7,X5,X8),k6_relat_1(X7)) | k1_xboole_0 = X6 | k1_xboole_0 = X7 | k2_funct_1(X5) = X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(X8,X6,X7) | ~v1_funct_1(X8) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~v1_funct_2(X5,X7,X6) | ~v1_funct_1(X5) | ~v2_funct_2(X5,X6) | ~v5_relat_1(X5,X6) | ~v1_relat_1(X5)) )),
% 1.57/0.60    inference(superposition,[],[f531,f90])).
% 1.57/0.60  fof(f531,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~r2_relset_1(X2,X2,k1_partfun1(X2,k2_relat_1(X0),k2_relat_1(X0),X2,X0,X1),k6_relat_1(X2)) | k2_relat_1(X0) = k1_xboole_0 | k1_xboole_0 = X2 | k2_funct_1(X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X0),X2))) | ~v1_funct_2(X1,k2_relat_1(X0),X2) | ~v1_funct_1(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,k2_relat_1(X0)))) | ~v1_funct_2(X0,X2,k2_relat_1(X0)) | ~v1_funct_1(X0)) )),
% 1.57/0.60    inference(equality_resolution,[],[f384])).
% 1.57/0.60  fof(f384,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.60    inference(duplicate_literal_removal,[],[f383])).
% 1.57/0.60  fof(f383,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (k2_relat_1(X2) != X1 | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(superposition,[],[f382,f89])).
% 1.57/0.60  fof(f89,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f45])).
% 1.57/0.60  fof(f45,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f11])).
% 1.57/0.60  fof(f11,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.57/0.60  fof(f382,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.60    inference(subsumption_resolution,[],[f381,f353])).
% 1.57/0.60  fof(f353,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | v2_funct_1(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f70,f72])).
% 1.57/0.60  fof(f72,plain,(
% 1.57/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f18])).
% 1.57/0.60  fof(f18,axiom,(
% 1.57/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.57/0.60  fof(f70,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f33])).
% 1.57/0.60  fof(f33,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.60    inference(flattening,[],[f32])).
% 1.57/0.60  fof(f32,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.60    inference(ennf_transformation,[],[f19])).
% 1.57/0.60  fof(f19,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.57/0.60  fof(f381,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_relat_1(X0)) | k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.60    inference(forward_demodulation,[],[f69,f72])).
% 1.57/0.60  fof(f69,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f31])).
% 1.57/0.60  fof(f31,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (! [X3] : (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.57/0.60    inference(flattening,[],[f30])).
% 1.57/0.60  fof(f30,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (! [X3] : (((k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | (~v2_funct_1(X2) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.57/0.60    inference(ennf_transformation,[],[f20])).
% 1.57/0.60  fof(f20,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.57/0.60  fof(f519,plain,(
% 1.57/0.60    spl3_48 | ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_47),
% 1.57/0.60    inference(avatar_split_clause,[],[f514,f467,f144,f129,f124,f109,f516])).
% 1.57/0.60  fof(f516,plain,(
% 1.57/0.60    spl3_48 <=> v1_funct_1(k6_relat_1(sK0))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 1.57/0.60  fof(f514,plain,(
% 1.57/0.60    v1_funct_1(k6_relat_1(sK0)) | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f513,f146])).
% 1.57/0.60  fof(f513,plain,(
% 1.57/0.60    v1_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f512,f131])).
% 1.57/0.60  fof(f512,plain,(
% 1.57/0.60    v1_funct_1(k6_relat_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f511,f126])).
% 1.57/0.60  fof(f511,plain,(
% 1.57/0.60    v1_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_47)),
% 1.57/0.60    inference(subsumption_resolution,[],[f508,f111])).
% 1.57/0.60  fof(f508,plain,(
% 1.57/0.60    v1_funct_1(k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | ~spl3_47),
% 1.57/0.60    inference(superposition,[],[f73,f469])).
% 1.57/0.60  fof(f73,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f35])).
% 1.57/0.60  fof(f35,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.57/0.60    inference(flattening,[],[f34])).
% 1.57/0.60  fof(f34,plain,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.57/0.60    inference(ennf_transformation,[],[f16])).
% 1.57/0.60  fof(f16,axiom,(
% 1.57/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.57/0.60  fof(f478,plain,(
% 1.57/0.60    ~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | spl3_46),
% 1.57/0.60    inference(avatar_contradiction_clause,[],[f477])).
% 1.57/0.60  fof(f477,plain,(
% 1.57/0.60    $false | (~spl3_3 | ~spl3_6 | ~spl3_7 | ~spl3_10 | spl3_46)),
% 1.57/0.60    inference(subsumption_resolution,[],[f476,f146])).
% 1.57/0.60  fof(f476,plain,(
% 1.57/0.60    ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6 | ~spl3_7 | spl3_46)),
% 1.57/0.60    inference(subsumption_resolution,[],[f475,f131])).
% 1.57/0.60  fof(f475,plain,(
% 1.57/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | ~spl3_6 | spl3_46)),
% 1.57/0.60    inference(subsumption_resolution,[],[f474,f126])).
% 1.57/0.60  fof(f474,plain,(
% 1.57/0.60    ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | (~spl3_3 | spl3_46)),
% 1.57/0.60    inference(subsumption_resolution,[],[f472,f111])).
% 1.57/0.60  fof(f472,plain,(
% 1.57/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK1) | spl3_46),
% 1.57/0.60    inference(resolution,[],[f465,f74])).
% 1.57/0.60  fof(f74,plain,(
% 1.57/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f35])).
% 1.57/0.60  fof(f465,plain,(
% 1.57/0.60    ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl3_46),
% 1.57/0.60    inference(avatar_component_clause,[],[f463])).
% 1.57/0.60  fof(f463,plain,(
% 1.57/0.60    spl3_46 <=> m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.57/0.60  fof(f470,plain,(
% 1.57/0.60    ~spl3_46 | spl3_47 | ~spl3_14),
% 1.57/0.60    inference(avatar_split_clause,[],[f459,f167,f467,f463])).
% 1.57/0.60  fof(f167,plain,(
% 1.57/0.60    spl3_14 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.57/0.60  fof(f459,plain,(
% 1.57/0.60    k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl3_14),
% 1.57/0.60    inference(resolution,[],[f312,f169])).
% 1.57/0.60  fof(f169,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~spl3_14),
% 1.57/0.60    inference(avatar_component_clause,[],[f167])).
% 1.57/0.60  fof(f312,plain,(
% 1.57/0.60    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.57/0.60    inference(resolution,[],[f67,f79])).
% 1.57/0.60  fof(f67,plain,(
% 1.57/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.57/0.60    inference(cnf_transformation,[],[f54])).
% 1.57/0.60  fof(f377,plain,(
% 1.57/0.60    ~spl3_36 | spl3_37 | ~spl3_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f358,f109,f374,f370])).
% 1.57/0.60  fof(f370,plain,(
% 1.57/0.60    spl3_36 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.57/0.60  fof(f374,plain,(
% 1.57/0.60    spl3_37 <=> sK2 = k6_relat_1(sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.57/0.60  fof(f358,plain,(
% 1.57/0.60    sK2 = k6_relat_1(sK0) | ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),sK2) | ~spl3_3),
% 1.57/0.60    inference(resolution,[],[f310,f79])).
% 1.57/0.60  fof(f310,plain,(
% 1.57/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | sK2 = X0 | ~r2_relset_1(sK0,sK0,X0,sK2)) ) | ~spl3_3),
% 1.57/0.60    inference(resolution,[],[f67,f111])).
% 1.57/0.60  fof(f331,plain,(
% 1.57/0.60    spl3_32 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_10),
% 1.57/0.60    inference(avatar_split_clause,[],[f326,f144,f139,f134,f129,f328])).
% 1.57/0.60  fof(f328,plain,(
% 1.57/0.60    spl3_32 <=> k2_funct_2(sK0,sK1) = k2_funct_1(sK1)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.57/0.60  fof(f134,plain,(
% 1.57/0.60    spl3_8 <=> v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.57/0.60  fof(f326,plain,(
% 1.57/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | (~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_10)),
% 1.57/0.60    inference(subsumption_resolution,[],[f325,f146])).
% 1.57/0.60  fof(f325,plain,(
% 1.57/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_1(sK1) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 1.57/0.60    inference(subsumption_resolution,[],[f324,f141])).
% 1.57/0.60  fof(f324,plain,(
% 1.57/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | (~spl3_7 | ~spl3_8)),
% 1.57/0.60    inference(subsumption_resolution,[],[f314,f136])).
% 1.57/0.60  fof(f136,plain,(
% 1.57/0.60    v3_funct_2(sK1,sK0,sK0) | ~spl3_8),
% 1.57/0.60    inference(avatar_component_clause,[],[f134])).
% 1.57/0.60  fof(f314,plain,(
% 1.57/0.60    k2_funct_2(sK0,sK1) = k2_funct_1(sK1) | ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | ~spl3_7),
% 1.57/0.60    inference(resolution,[],[f66,f131])).
% 1.57/0.60  fof(f306,plain,(
% 1.57/0.60    spl3_30 | ~spl3_7 | ~spl3_8 | ~spl3_10),
% 1.57/0.60    inference(avatar_split_clause,[],[f301,f144,f134,f129,f303])).
% 1.57/0.60  fof(f301,plain,(
% 1.57/0.60    v2_funct_2(sK1,sK0) | (~spl3_7 | ~spl3_8 | ~spl3_10)),
% 1.57/0.60    inference(subsumption_resolution,[],[f300,f146])).
% 1.57/0.60  fof(f300,plain,(
% 1.57/0.60    ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | (~spl3_7 | ~spl3_8)),
% 1.57/0.60    inference(subsumption_resolution,[],[f291,f136])).
% 1.57/0.60  fof(f291,plain,(
% 1.57/0.60    ~v3_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1) | v2_funct_2(sK1,sK0) | ~spl3_7),
% 1.57/0.60    inference(resolution,[],[f77,f131])).
% 1.57/0.60  fof(f77,plain,(
% 1.57/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v2_funct_2(X2,X1)) )),
% 1.57/0.60    inference(cnf_transformation,[],[f37])).
% 1.57/0.60  fof(f37,plain,(
% 1.57/0.60    ! [X0,X1,X2] : ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | ~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(flattening,[],[f36])).
% 1.57/0.60  fof(f36,plain,(
% 1.57/0.60    ! [X0,X1,X2] : (((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) | (~v3_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.57/0.60    inference(ennf_transformation,[],[f14])).
% 1.57/0.60  fof(f14,axiom,(
% 1.57/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).
% 1.57/0.60  fof(f299,plain,(
% 1.57/0.60    spl3_29 | ~spl3_3 | ~spl3_4 | ~spl3_6),
% 1.57/0.60    inference(avatar_split_clause,[],[f294,f124,f114,f109,f296])).
% 1.57/0.60  fof(f114,plain,(
% 1.57/0.60    spl3_4 <=> v3_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.57/0.60  fof(f294,plain,(
% 1.57/0.60    v2_funct_2(sK2,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 1.57/0.60    inference(subsumption_resolution,[],[f293,f126])).
% 1.57/0.60  fof(f293,plain,(
% 1.57/0.60    ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0) | (~spl3_3 | ~spl3_4)),
% 1.57/0.60    inference(subsumption_resolution,[],[f290,f116])).
% 1.57/0.60  fof(f116,plain,(
% 1.57/0.60    v3_funct_2(sK2,sK0,sK0) | ~spl3_4),
% 1.57/0.60    inference(avatar_component_clause,[],[f114])).
% 1.57/0.60  fof(f290,plain,(
% 1.57/0.60    ~v3_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2) | v2_funct_2(sK2,sK0) | ~spl3_3),
% 1.57/0.60    inference(resolution,[],[f77,f111])).
% 1.57/0.60  fof(f251,plain,(
% 1.57/0.60    spl3_25 | ~spl3_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f244,f109,f248])).
% 1.57/0.60  fof(f248,plain,(
% 1.57/0.60    spl3_25 <=> r2_relset_1(sK0,sK0,sK2,sK2)),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.57/0.60  fof(f244,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,sK2,sK2) | ~spl3_3),
% 1.57/0.60    inference(resolution,[],[f97,f111])).
% 1.57/0.60  fof(f229,plain,(
% 1.57/0.60    spl3_22 | ~spl3_7),
% 1.57/0.60    inference(avatar_split_clause,[],[f218,f129,f226])).
% 1.57/0.60  fof(f218,plain,(
% 1.57/0.60    v5_relat_1(sK1,sK0) | ~spl3_7),
% 1.57/0.60    inference(resolution,[],[f94,f131])).
% 1.57/0.60  fof(f224,plain,(
% 1.57/0.60    spl3_21 | ~spl3_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f217,f109,f221])).
% 1.57/0.60  fof(f217,plain,(
% 1.57/0.60    v5_relat_1(sK2,sK0) | ~spl3_3),
% 1.57/0.60    inference(resolution,[],[f94,f111])).
% 1.57/0.60  fof(f201,plain,(
% 1.57/0.60    spl3_19 | ~spl3_7),
% 1.57/0.60    inference(avatar_split_clause,[],[f190,f129,f198])).
% 1.57/0.60  fof(f190,plain,(
% 1.57/0.60    v1_relat_1(sK1) | ~spl3_7),
% 1.57/0.60    inference(resolution,[],[f78,f131])).
% 1.57/0.60  fof(f196,plain,(
% 1.57/0.60    spl3_18 | ~spl3_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f189,f109,f193])).
% 1.57/0.60  fof(f189,plain,(
% 1.57/0.60    v1_relat_1(sK2) | ~spl3_3),
% 1.57/0.60    inference(resolution,[],[f78,f111])).
% 1.57/0.60  fof(f170,plain,(
% 1.57/0.60    spl3_14 | ~spl3_2),
% 1.57/0.60    inference(avatar_split_clause,[],[f165,f104,f167])).
% 1.57/0.60  fof(f104,plain,(
% 1.57/0.60    spl3_2 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.57/0.60  fof(f165,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_relat_1(sK0)) | ~spl3_2),
% 1.57/0.60    inference(backward_demodulation,[],[f106,f72])).
% 1.57/0.60  fof(f106,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) | ~spl3_2),
% 1.57/0.60    inference(avatar_component_clause,[],[f104])).
% 1.57/0.60  fof(f152,plain,(
% 1.57/0.60    spl3_11),
% 1.57/0.60    inference(avatar_split_clause,[],[f86,f149])).
% 1.57/0.60  fof(f86,plain,(
% 1.57/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.57/0.60    inference(cnf_transformation,[],[f5])).
% 1.57/0.60  fof(f5,axiom,(
% 1.57/0.60    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.57/0.60  fof(f147,plain,(
% 1.57/0.60    spl3_10),
% 1.57/0.60    inference(avatar_split_clause,[],[f56,f144])).
% 1.57/0.60  fof(f56,plain,(
% 1.57/0.60    v1_funct_1(sK1)),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f53,plain,(
% 1.57/0.60    (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 1.57/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f52,f51])).
% 1.57/0.60  fof(f51,plain,(
% 1.57/0.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK1,sK0,sK0) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f52,plain,(
% 1.57/0.60    ? [X2] : (~r2_relset_1(sK0,sK0,X2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,X2),k6_partfun1(sK0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(X2,sK0,sK0) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v3_funct_2(sK2,sK0,sK0) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 1.57/0.60    introduced(choice_axiom,[])).
% 1.57/0.60  fof(f25,plain,(
% 1.57/0.60    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.57/0.60    inference(flattening,[],[f24])).
% 1.57/0.60  fof(f24,plain,(
% 1.57/0.60    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.57/0.60    inference(ennf_transformation,[],[f22])).
% 1.57/0.60  fof(f22,negated_conjecture,(
% 1.57/0.60    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.57/0.60    inference(negated_conjecture,[],[f21])).
% 1.57/0.60  fof(f21,conjecture,(
% 1.57/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X2,X0,X0) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),k6_partfun1(X0)) => r2_relset_1(X0,X0,X2,k2_funct_2(X0,X1)))))),
% 1.57/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_2)).
% 1.57/0.60  fof(f142,plain,(
% 1.57/0.60    spl3_9),
% 1.57/0.60    inference(avatar_split_clause,[],[f57,f139])).
% 1.57/0.60  fof(f57,plain,(
% 1.57/0.60    v1_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f137,plain,(
% 1.57/0.60    spl3_8),
% 1.57/0.60    inference(avatar_split_clause,[],[f58,f134])).
% 1.57/0.60  fof(f58,plain,(
% 1.57/0.60    v3_funct_2(sK1,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f132,plain,(
% 1.57/0.60    spl3_7),
% 1.57/0.60    inference(avatar_split_clause,[],[f59,f129])).
% 1.57/0.60  fof(f59,plain,(
% 1.57/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f127,plain,(
% 1.57/0.60    spl3_6),
% 1.57/0.60    inference(avatar_split_clause,[],[f60,f124])).
% 1.57/0.60  fof(f60,plain,(
% 1.57/0.60    v1_funct_1(sK2)),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f122,plain,(
% 1.57/0.60    spl3_5),
% 1.57/0.60    inference(avatar_split_clause,[],[f61,f119])).
% 1.57/0.60  fof(f61,plain,(
% 1.57/0.60    v1_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f117,plain,(
% 1.57/0.60    spl3_4),
% 1.57/0.60    inference(avatar_split_clause,[],[f62,f114])).
% 1.57/0.60  fof(f62,plain,(
% 1.57/0.60    v3_funct_2(sK2,sK0,sK0)),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f112,plain,(
% 1.57/0.60    spl3_3),
% 1.57/0.60    inference(avatar_split_clause,[],[f63,f109])).
% 1.57/0.60  fof(f63,plain,(
% 1.57/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f107,plain,(
% 1.57/0.60    spl3_2),
% 1.57/0.60    inference(avatar_split_clause,[],[f64,f104])).
% 1.57/0.60  fof(f64,plain,(
% 1.57/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2),k6_partfun1(sK0))),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  fof(f102,plain,(
% 1.57/0.60    ~spl3_1),
% 1.57/0.60    inference(avatar_split_clause,[],[f65,f99])).
% 1.57/0.60  fof(f99,plain,(
% 1.57/0.60    spl3_1 <=> r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.57/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.57/0.60  fof(f65,plain,(
% 1.57/0.60    ~r2_relset_1(sK0,sK0,sK2,k2_funct_2(sK0,sK1))),
% 1.57/0.60    inference(cnf_transformation,[],[f53])).
% 1.57/0.60  % SZS output end Proof for theBenchmark
% 1.57/0.60  % (14322)------------------------------
% 1.57/0.60  % (14322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.60  % (14322)Termination reason: Refutation
% 1.57/0.60  
% 1.57/0.60  % (14322)Memory used [KB]: 7164
% 1.57/0.60  % (14322)Time elapsed: 0.186 s
% 1.57/0.60  % (14322)------------------------------
% 1.57/0.60  % (14322)------------------------------
% 1.57/0.60  % (14300)Success in time 0.243 s
%------------------------------------------------------------------------------
