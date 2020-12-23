%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:31 EST 2020

% Result     : Theorem 1.90s
% Output     : Refutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :  276 ( 658 expanded)
%              Number of leaves         :   58 ( 244 expanded)
%              Depth                    :    9
%              Number of atoms          :  980 (2828 expanded)
%              Number of equality atoms :  182 ( 810 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1022,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f135,f180,f182,f184,f186,f194,f213,f237,f239,f241,f255,f283,f287,f299,f303,f379,f429,f439,f453,f466,f493,f573,f609,f642,f670,f679,f709,f733,f737,f747,f756,f763,f901,f909,f915,f955,f982,f989,f997,f1004,f1008,f1019])).

fof(f1019,plain,
    ( ~ spl4_15
    | ~ spl4_66 ),
    inference(avatar_contradiction_clause,[],[f1012])).

fof(f1012,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_66 ),
    inference(subsumption_resolution,[],[f51,f1011])).

fof(f1011,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_15
    | ~ spl4_66 ),
    inference(forward_demodulation,[],[f688,f262])).

fof(f262,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl4_15
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f688,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl4_66
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f51,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f1008,plain,
    ( ~ spl4_15
    | ~ spl4_47
    | spl4_71 ),
    inference(avatar_contradiction_clause,[],[f1007])).

fof(f1007,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_47
    | spl4_71 ),
    inference(trivial_inequality_removal,[],[f1006])).

fof(f1006,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_15
    | ~ spl4_47
    | spl4_71 ),
    inference(forward_demodulation,[],[f1005,f513])).

fof(f513,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f500,f86])).

fof(f86,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f500,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_47 ),
    inference(superposition,[],[f86,f491])).

fof(f491,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f489])).

fof(f489,plain,
    ( spl4_47
  <=> k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f1005,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_15
    | spl4_71 ),
    inference(forward_demodulation,[],[f708,f262])).

fof(f708,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_71 ),
    inference(avatar_component_clause,[],[f706])).

fof(f706,plain,
    ( spl4_71
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f1004,plain,
    ( ~ spl4_15
    | spl4_69 ),
    inference(avatar_contradiction_clause,[],[f1001])).

fof(f1001,plain,
    ( $false
    | ~ spl4_15
    | spl4_69 ),
    inference(subsumption_resolution,[],[f48,f998])).

fof(f998,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_15
    | spl4_69 ),
    inference(forward_demodulation,[],[f700,f262])).

fof(f700,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f698])).

fof(f698,plain,
    ( spl4_69
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f48,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f997,plain,
    ( ~ spl4_15
    | ~ spl4_32
    | ~ spl4_61
    | spl4_68 ),
    inference(avatar_contradiction_clause,[],[f996])).

fof(f996,plain,
    ( $false
    | ~ spl4_15
    | ~ spl4_32
    | ~ spl4_61
    | spl4_68 ),
    inference(subsumption_resolution,[],[f418,f991])).

fof(f991,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_15
    | ~ spl4_61
    | spl4_68 ),
    inference(forward_demodulation,[],[f990,f656])).

fof(f656,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f654])).

fof(f654,plain,
    ( spl4_61
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f990,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_15
    | spl4_68 ),
    inference(forward_demodulation,[],[f696,f262])).

fof(f696,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | spl4_68 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_68
  <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f418,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f409,f86])).

fof(f409,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_32 ),
    inference(superposition,[],[f86,f377])).

fof(f377,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl4_32
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f989,plain,
    ( ~ spl4_15
    | spl4_67 ),
    inference(avatar_contradiction_clause,[],[f986])).

fof(f986,plain,
    ( $false
    | ~ spl4_15
    | spl4_67 ),
    inference(subsumption_resolution,[],[f97,f969])).

fof(f969,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_15
    | spl4_67 ),
    inference(superposition,[],[f692,f262])).

fof(f692,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_67 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl4_67
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f97,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f982,plain,
    ( ~ spl4_15
    | spl4_70 ),
    inference(avatar_contradiction_clause,[],[f981])).

fof(f981,plain,
    ( $false
    | ~ spl4_15
    | spl4_70 ),
    inference(subsumption_resolution,[],[f52,f968])).

fof(f968,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_15
    | spl4_70 ),
    inference(superposition,[],[f704,f262])).

fof(f704,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_70 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl4_70
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f955,plain,
    ( spl4_17
    | ~ spl4_47
    | ~ spl4_87 ),
    inference(avatar_contradiction_clause,[],[f950])).

fof(f950,plain,
    ( $false
    | spl4_17
    | ~ spl4_47
    | ~ spl4_87 ),
    inference(subsumption_resolution,[],[f540,f934])).

fof(f934,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_87 ),
    inference(forward_demodulation,[],[f922,f86])).

fof(f922,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_87 ),
    inference(superposition,[],[f86,f913])).

fof(f913,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f911])).

fof(f911,plain,
    ( spl4_87
  <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f540,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_17
    | ~ spl4_47 ),
    inference(superposition,[],[f270,f513])).

fof(f270,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl4_17
  <=> k2_relat_1(sK2) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f915,plain,
    ( ~ spl4_16
    | ~ spl4_18
    | ~ spl4_5
    | spl4_87
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f682,f606,f911,f152,f272,f264])).

fof(f264,plain,
    ( spl4_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f272,plain,
    ( spl4_18
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f152,plain,
    ( spl4_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f606,plain,
    ( spl4_59
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f682,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_59 ),
    inference(superposition,[],[f608,f89])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f61,f55])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f608,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f606])).

fof(f909,plain,(
    spl4_85 ),
    inference(avatar_contradiction_clause,[],[f906])).

fof(f906,plain,
    ( $false
    | spl4_85 ),
    inference(unit_resulting_resolution,[],[f84,f900])).

fof(f900,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_85 ),
    inference(avatar_component_clause,[],[f898])).

fof(f898,plain,
    ( spl4_85
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f55])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f901,plain,
    ( ~ spl4_43
    | ~ spl4_4
    | ~ spl4_5
    | spl4_58
    | spl4_18
    | ~ spl4_85
    | ~ spl4_2
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f894,f668,f132,f898,f272,f601,f152,f148,f450])).

fof(f450,plain,
    ( spl4_43
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f148,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f601,plain,
    ( spl4_58
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f132,plain,
    ( spl4_2
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f668,plain,
    ( spl4_63
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f894,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_2
    | ~ spl4_63 ),
    inference(superposition,[],[f669,f134])).

fof(f134,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f132])).

fof(f669,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f668])).

fof(f763,plain,
    ( spl4_20
    | ~ spl4_61 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl4_20
    | ~ spl4_61 ),
    inference(trivial_inequality_removal,[],[f759])).

fof(f759,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_20
    | ~ spl4_61 ),
    inference(superposition,[],[f282,f656])).

fof(f282,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl4_20
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f756,plain,
    ( ~ spl4_42
    | ~ spl4_74 ),
    inference(avatar_contradiction_clause,[],[f754])).

fof(f754,plain,
    ( $false
    | ~ spl4_42
    | ~ spl4_74 ),
    inference(unit_resulting_resolution,[],[f102,f448,f104,f746])).

fof(f746,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k6_partfun1(sK0),X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) )
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f745])).

fof(f745,plain,
    ( spl4_74
  <=> ! [X0] :
        ( ~ v5_relat_1(k6_partfun1(sK0),X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f104,plain,(
    ! [X0] : v5_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f68,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f55])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f448,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl4_42
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f102,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f68,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f747,plain,
    ( ~ spl4_16
    | spl4_74
    | spl4_30 ),
    inference(avatar_split_clause,[],[f743,f356,f745,f264])).

fof(f356,plain,
    ( spl4_30
  <=> v5_relat_1(k6_partfun1(sK0),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(k6_partfun1(sK0),X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | ~ v2_funct_2(sK3,X0) )
    | spl4_30 ),
    inference(superposition,[],[f358,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f358,plain,
    ( ~ v5_relat_1(k6_partfun1(sK0),k2_relat_1(sK3))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f356])).

fof(f737,plain,
    ( spl4_61
    | ~ spl4_29
    | ~ spl4_30
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f734,f348,f356,f352,f654])).

fof(f352,plain,
    ( spl4_29
  <=> v1_relat_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f348,plain,
    ( spl4_28
  <=> v2_funct_2(k6_partfun1(sK0),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f734,plain,
    ( ~ v5_relat_1(k6_partfun1(sK0),k2_relat_1(sK3))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3)
    | ~ spl4_28 ),
    inference(resolution,[],[f350,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_2(k6_partfun1(X0),X1)
      | ~ v5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | X0 = X1 ) ),
    inference(superposition,[],[f65,f86])).

fof(f350,plain,
    ( v2_funct_2(k6_partfun1(sK0),k2_relat_1(sK3))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f348])).

fof(f733,plain,
    ( ~ spl4_32
    | ~ spl4_39
    | ~ spl4_42
    | ~ spl4_65 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | ~ spl4_32
    | ~ spl4_39
    | ~ spl4_42
    | ~ spl4_65 ),
    inference(unit_resulting_resolution,[],[f102,f448,f482,f678])).

fof(f678,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(k6_partfun1(sK0),X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) )
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f677])).

fof(f677,plain,
    ( spl4_65
  <=> ! [X0] :
        ( ~ v2_funct_2(k6_partfun1(sK0),X0)
        | ~ v2_funct_2(sK3,X0)
        | ~ v5_relat_1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f482,plain,
    ( v2_funct_2(k6_partfun1(sK0),sK0)
    | ~ spl4_32
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f423,f418])).

fof(f423,plain,
    ( v2_funct_2(k6_partfun1(sK0),k1_relat_1(sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl4_39
  <=> v2_funct_2(k6_partfun1(sK0),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f709,plain,
    ( spl4_66
    | ~ spl4_67
    | ~ spl4_68
    | ~ spl4_69
    | ~ spl4_5
    | ~ spl4_16
    | ~ spl4_70
    | ~ spl4_71
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f684,f606,f706,f702,f264,f152,f698,f694,f690,f686])).

fof(f684,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_59 ),
    inference(superposition,[],[f90,f608])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f63,f55])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
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
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f679,plain,
    ( ~ spl4_16
    | spl4_65
    | spl4_28 ),
    inference(avatar_split_clause,[],[f675,f348,f677,f264])).

fof(f675,plain,
    ( ! [X0] :
        ( ~ v2_funct_2(k6_partfun1(sK0),X0)
        | ~ v5_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3)
        | ~ v2_funct_2(sK3,X0) )
    | spl4_28 ),
    inference(superposition,[],[f349,f65])).

fof(f349,plain,
    ( ~ v2_funct_2(k6_partfun1(sK0),k2_relat_1(sK3))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f348])).

fof(f670,plain,
    ( ~ spl4_3
    | spl4_63
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f666,f234,f156,f668,f144])).

fof(f144,plain,
    ( spl4_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f156,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f234,plain,
    ( spl4_14
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f666,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f663])).

fof(f663,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f77,f46])).

fof(f46,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f642,plain,(
    ~ spl4_58 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | ~ spl4_58 ),
    inference(subsumption_resolution,[],[f49,f603])).

fof(f603,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_58 ),
    inference(avatar_component_clause,[],[f601])).

fof(f49,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

fof(f609,plain,
    ( spl4_59
    | spl4_58
    | ~ spl4_18
    | ~ spl4_5
    | ~ spl4_4
    | ~ spl4_43
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f594,f570,f450,f148,f152,f272,f601,f606])).

fof(f570,plain,
    ( spl4_56
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f594,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_56 ),
    inference(trivial_inequality_removal,[],[f593])).

fof(f593,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_56 ),
    inference(superposition,[],[f69,f572])).

fof(f572,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f570])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f573,plain,
    ( spl4_56
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f563,f450,f148,f144,f234,f156,f152,f570])).

fof(f563,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f493,plain,
    ( ~ spl4_19
    | ~ spl4_13
    | ~ spl4_3
    | spl4_47
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f486,f296,f489,f144,f230,f276])).

fof(f276,plain,
    ( spl4_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f230,plain,
    ( spl4_13
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f296,plain,
    ( spl4_22
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f486,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_22 ),
    inference(superposition,[],[f88,f298])).

fof(f298,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f296])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f55])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f466,plain,(
    spl4_43 ),
    inference(avatar_contradiction_clause,[],[f465])).

fof(f465,plain,
    ( $false
    | spl4_43 ),
    inference(subsumption_resolution,[],[f44,f452])).

fof(f452,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_43 ),
    inference(avatar_component_clause,[],[f450])).

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f453,plain,
    ( spl4_42
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_43
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f440,f234,f156,f152,f450,f148,f144,f446])).

fof(f440,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK3,sK0) ),
    inference(resolution,[],[f73,f47])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | v2_funct_2(X3,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f439,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f435])).

fof(f435,plain,
    ( $false
    | spl4_29 ),
    inference(unit_resulting_resolution,[],[f83,f354,f66])).

fof(f354,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f352])).

fof(f429,plain,
    ( ~ spl4_29
    | spl4_39
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f415,f375,f421,f352])).

fof(f415,plain,
    ( v2_funct_2(k6_partfun1(sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ spl4_32 ),
    inference(superposition,[],[f109,f377])).

fof(f109,plain,(
    ! [X0] :
      ( v2_funct_2(k6_partfun1(X0),X0)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f105,f104])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v5_relat_1(k6_partfun1(X0),X0)
      | ~ v1_relat_1(k6_partfun1(X0))
      | v2_funct_2(k6_partfun1(X0),X0) ) ),
    inference(superposition,[],[f91,f86])).

fof(f91,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f379,plain,
    ( ~ spl4_19
    | ~ spl4_13
    | ~ spl4_3
    | spl4_32
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f372,f222,f375,f144,f230,f276])).

fof(f222,plain,
    ( spl4_11
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f372,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_11 ),
    inference(superposition,[],[f89,f224])).

fof(f224,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f222])).

fof(f303,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f97,f278])).

fof(f278,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f276])).

fof(f299,plain,
    ( spl4_22
    | spl4_12
    | ~ spl4_13
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f294,f234,f156,f144,f230,f226,f296])).

fof(f226,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f294,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(trivial_inequality_removal,[],[f293])).

fof(f293,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(superposition,[],[f70,f46])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f287,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | spl4_16 ),
    inference(subsumption_resolution,[],[f96,f266])).

fof(f266,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f264])).

fof(f96,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f45])).

fof(f283,plain,
    ( spl4_15
    | ~ spl4_16
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_3
    | ~ spl4_19
    | ~ spl4_5
    | ~ spl4_20
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f258,f203,f280,f152,f276,f144,f272,f268,f264,f260])).

fof(f203,plain,
    ( spl4_9
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f258,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_9 ),
    inference(superposition,[],[f90,f205])).

fof(f205,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f203])).

fof(f255,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f242])).

fof(f242,plain,
    ( $false
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f50,f228])).

fof(f228,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f226])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f241,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f53,f236])).

fof(f236,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f234])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f239,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f48,f232])).

fof(f232,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f230])).

fof(f237,plain,
    ( spl4_11
    | spl4_12
    | ~ spl4_13
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f220,f234,f156,f144,f230,f226,f222])).

fof(f220,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f219])).

fof(f219,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f69,f46])).

fof(f213,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f210,f132,f203,f156,f152,f148,f144])).

fof(f210,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f80,f134])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f194,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f54,f158])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f186,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f43,f154])).

fof(f154,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f184,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f45,f150])).

fof(f150,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f148])).

fof(f182,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f52,f146])).

fof(f146,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f180,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f52,f43,f45,f54,f130,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f130,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl4_1
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f135,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f125,f132,f128])).

fof(f125,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f122,f47])).

fof(f122,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f79,f83])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (27773)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.48  % (27791)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (27769)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (27774)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.56  % (27783)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (27787)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (27771)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (27772)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.57  % (27797)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (27777)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (27778)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.57  % (27798)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (27781)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (27799)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.58  % (27790)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.58  % (27792)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.58  % (27789)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (27786)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.58  % (27801)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.58  % (27782)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (27779)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.58  % (27780)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.58  % (27800)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.58  % (27794)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.59  % (27776)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  % (27775)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.59  % (27796)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.59  % (27785)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (27795)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.60  % (27784)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.90/0.60  % (27786)Refutation not found, incomplete strategy% (27786)------------------------------
% 1.90/0.60  % (27786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.60  % (27786)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.60  
% 1.90/0.60  % (27786)Memory used [KB]: 10746
% 1.90/0.60  % (27786)Time elapsed: 0.179 s
% 1.90/0.60  % (27786)------------------------------
% 1.90/0.60  % (27786)------------------------------
% 1.90/0.62  % (27783)Refutation found. Thanks to Tanya!
% 1.90/0.62  % SZS status Theorem for theBenchmark
% 1.90/0.62  % SZS output start Proof for theBenchmark
% 1.90/0.62  fof(f1022,plain,(
% 1.90/0.62    $false),
% 1.90/0.62    inference(avatar_sat_refutation,[],[f135,f180,f182,f184,f186,f194,f213,f237,f239,f241,f255,f283,f287,f299,f303,f379,f429,f439,f453,f466,f493,f573,f609,f642,f670,f679,f709,f733,f737,f747,f756,f763,f901,f909,f915,f955,f982,f989,f997,f1004,f1008,f1019])).
% 1.90/0.62  fof(f1019,plain,(
% 1.90/0.62    ~spl4_15 | ~spl4_66),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f1012])).
% 1.90/0.62  fof(f1012,plain,(
% 1.90/0.62    $false | (~spl4_15 | ~spl4_66)),
% 1.90/0.62    inference(subsumption_resolution,[],[f51,f1011])).
% 1.90/0.62  fof(f1011,plain,(
% 1.90/0.62    sK3 = k2_funct_1(sK2) | (~spl4_15 | ~spl4_66)),
% 1.90/0.62    inference(forward_demodulation,[],[f688,f262])).
% 1.90/0.62  fof(f262,plain,(
% 1.90/0.62    sK2 = k2_funct_1(sK3) | ~spl4_15),
% 1.90/0.62    inference(avatar_component_clause,[],[f260])).
% 1.90/0.62  fof(f260,plain,(
% 1.90/0.62    spl4_15 <=> sK2 = k2_funct_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.90/0.62  fof(f688,plain,(
% 1.90/0.62    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_66),
% 1.90/0.62    inference(avatar_component_clause,[],[f686])).
% 1.90/0.62  fof(f686,plain,(
% 1.90/0.62    spl4_66 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 1.90/0.62  fof(f51,plain,(
% 1.90/0.62    sK3 != k2_funct_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f20,plain,(
% 1.90/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f19])).
% 1.90/0.62  fof(f19,plain,(
% 1.90/0.62    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f18])).
% 1.90/0.62  fof(f18,negated_conjecture,(
% 1.90/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.90/0.62    inference(negated_conjecture,[],[f17])).
% 1.90/0.62  fof(f17,conjecture,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.90/0.62  fof(f1008,plain,(
% 1.90/0.62    ~spl4_15 | ~spl4_47 | spl4_71),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f1007])).
% 1.90/0.62  fof(f1007,plain,(
% 1.90/0.62    $false | (~spl4_15 | ~spl4_47 | spl4_71)),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f1006])).
% 1.90/0.62  fof(f1006,plain,(
% 1.90/0.62    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_15 | ~spl4_47 | spl4_71)),
% 1.90/0.62    inference(forward_demodulation,[],[f1005,f513])).
% 1.90/0.62  fof(f513,plain,(
% 1.90/0.62    sK1 = k2_relat_1(sK2) | ~spl4_47),
% 1.90/0.62    inference(forward_demodulation,[],[f500,f86])).
% 1.90/0.62  fof(f86,plain,(
% 1.90/0.62    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.90/0.62    inference(definition_unfolding,[],[f60,f55])).
% 1.90/0.62  fof(f55,plain,(
% 1.90/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f12])).
% 1.90/0.62  fof(f12,axiom,(
% 1.90/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.90/0.62  fof(f60,plain,(
% 1.90/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.90/0.62    inference(cnf_transformation,[],[f1])).
% 1.90/0.62  fof(f1,axiom,(
% 1.90/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.90/0.62  fof(f500,plain,(
% 1.90/0.62    k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_47),
% 1.90/0.62    inference(superposition,[],[f86,f491])).
% 1.90/0.62  fof(f491,plain,(
% 1.90/0.62    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~spl4_47),
% 1.90/0.62    inference(avatar_component_clause,[],[f489])).
% 1.90/0.62  fof(f489,plain,(
% 1.90/0.62    spl4_47 <=> k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.90/0.62  fof(f1005,plain,(
% 1.90/0.62    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_15 | spl4_71)),
% 1.90/0.62    inference(forward_demodulation,[],[f708,f262])).
% 1.90/0.62  fof(f708,plain,(
% 1.90/0.62    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_71),
% 1.90/0.62    inference(avatar_component_clause,[],[f706])).
% 1.90/0.62  fof(f706,plain,(
% 1.90/0.62    spl4_71 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.90/0.62  fof(f1004,plain,(
% 1.90/0.62    ~spl4_15 | spl4_69),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f1001])).
% 1.90/0.62  fof(f1001,plain,(
% 1.90/0.62    $false | (~spl4_15 | spl4_69)),
% 1.90/0.62    inference(subsumption_resolution,[],[f48,f998])).
% 1.90/0.62  fof(f998,plain,(
% 1.90/0.62    ~v2_funct_1(sK2) | (~spl4_15 | spl4_69)),
% 1.90/0.62    inference(forward_demodulation,[],[f700,f262])).
% 1.90/0.62  fof(f700,plain,(
% 1.90/0.62    ~v2_funct_1(k2_funct_1(sK3)) | spl4_69),
% 1.90/0.62    inference(avatar_component_clause,[],[f698])).
% 1.90/0.62  fof(f698,plain,(
% 1.90/0.62    spl4_69 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.90/0.62  fof(f48,plain,(
% 1.90/0.62    v2_funct_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f997,plain,(
% 1.90/0.62    ~spl4_15 | ~spl4_32 | ~spl4_61 | spl4_68),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f996])).
% 1.90/0.62  fof(f996,plain,(
% 1.90/0.62    $false | (~spl4_15 | ~spl4_32 | ~spl4_61 | spl4_68)),
% 1.90/0.62    inference(subsumption_resolution,[],[f418,f991])).
% 1.90/0.62  fof(f991,plain,(
% 1.90/0.62    sK0 != k1_relat_1(sK2) | (~spl4_15 | ~spl4_61 | spl4_68)),
% 1.90/0.62    inference(forward_demodulation,[],[f990,f656])).
% 1.90/0.62  fof(f656,plain,(
% 1.90/0.62    sK0 = k2_relat_1(sK3) | ~spl4_61),
% 1.90/0.62    inference(avatar_component_clause,[],[f654])).
% 1.90/0.62  fof(f654,plain,(
% 1.90/0.62    spl4_61 <=> sK0 = k2_relat_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 1.90/0.62  fof(f990,plain,(
% 1.90/0.62    k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_15 | spl4_68)),
% 1.90/0.62    inference(forward_demodulation,[],[f696,f262])).
% 1.90/0.62  fof(f696,plain,(
% 1.90/0.62    k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | spl4_68),
% 1.90/0.62    inference(avatar_component_clause,[],[f694])).
% 1.90/0.62  fof(f694,plain,(
% 1.90/0.62    spl4_68 <=> k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 1.90/0.62  fof(f418,plain,(
% 1.90/0.62    sK0 = k1_relat_1(sK2) | ~spl4_32),
% 1.90/0.62    inference(forward_demodulation,[],[f409,f86])).
% 1.90/0.62  fof(f409,plain,(
% 1.90/0.62    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_32),
% 1.90/0.62    inference(superposition,[],[f86,f377])).
% 1.90/0.62  fof(f377,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_32),
% 1.90/0.62    inference(avatar_component_clause,[],[f375])).
% 1.90/0.62  fof(f375,plain,(
% 1.90/0.62    spl4_32 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.90/0.62  fof(f989,plain,(
% 1.90/0.62    ~spl4_15 | spl4_67),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f986])).
% 1.90/0.62  fof(f986,plain,(
% 1.90/0.62    $false | (~spl4_15 | spl4_67)),
% 1.90/0.62    inference(subsumption_resolution,[],[f97,f969])).
% 1.90/0.62  fof(f969,plain,(
% 1.90/0.62    ~v1_relat_1(sK2) | (~spl4_15 | spl4_67)),
% 1.90/0.62    inference(superposition,[],[f692,f262])).
% 1.90/0.62  fof(f692,plain,(
% 1.90/0.62    ~v1_relat_1(k2_funct_1(sK3)) | spl4_67),
% 1.90/0.62    inference(avatar_component_clause,[],[f690])).
% 1.90/0.62  fof(f690,plain,(
% 1.90/0.62    spl4_67 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 1.90/0.62  fof(f97,plain,(
% 1.90/0.62    v1_relat_1(sK2)),
% 1.90/0.62    inference(resolution,[],[f66,f54])).
% 1.90/0.62  fof(f54,plain,(
% 1.90/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f66,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f27])).
% 1.90/0.62  fof(f27,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(ennf_transformation,[],[f5])).
% 1.90/0.62  fof(f5,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.90/0.62  fof(f982,plain,(
% 1.90/0.62    ~spl4_15 | spl4_70),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f981])).
% 1.90/0.62  fof(f981,plain,(
% 1.90/0.62    $false | (~spl4_15 | spl4_70)),
% 1.90/0.62    inference(subsumption_resolution,[],[f52,f968])).
% 1.90/0.62  fof(f968,plain,(
% 1.90/0.62    ~v1_funct_1(sK2) | (~spl4_15 | spl4_70)),
% 1.90/0.62    inference(superposition,[],[f704,f262])).
% 1.90/0.62  fof(f704,plain,(
% 1.90/0.62    ~v1_funct_1(k2_funct_1(sK3)) | spl4_70),
% 1.90/0.62    inference(avatar_component_clause,[],[f702])).
% 1.90/0.62  fof(f702,plain,(
% 1.90/0.62    spl4_70 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 1.90/0.62  fof(f52,plain,(
% 1.90/0.62    v1_funct_1(sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f955,plain,(
% 1.90/0.62    spl4_17 | ~spl4_47 | ~spl4_87),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f950])).
% 1.90/0.62  fof(f950,plain,(
% 1.90/0.62    $false | (spl4_17 | ~spl4_47 | ~spl4_87)),
% 1.90/0.62    inference(subsumption_resolution,[],[f540,f934])).
% 1.90/0.62  fof(f934,plain,(
% 1.90/0.62    sK1 = k1_relat_1(sK3) | ~spl4_87),
% 1.90/0.62    inference(forward_demodulation,[],[f922,f86])).
% 1.90/0.62  fof(f922,plain,(
% 1.90/0.62    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_87),
% 1.90/0.62    inference(superposition,[],[f86,f913])).
% 1.90/0.62  fof(f913,plain,(
% 1.90/0.62    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~spl4_87),
% 1.90/0.62    inference(avatar_component_clause,[],[f911])).
% 1.90/0.62  fof(f911,plain,(
% 1.90/0.62    spl4_87 <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).
% 1.90/0.62  fof(f540,plain,(
% 1.90/0.62    sK1 != k1_relat_1(sK3) | (spl4_17 | ~spl4_47)),
% 1.90/0.62    inference(superposition,[],[f270,f513])).
% 1.90/0.62  fof(f270,plain,(
% 1.90/0.62    k2_relat_1(sK2) != k1_relat_1(sK3) | spl4_17),
% 1.90/0.62    inference(avatar_component_clause,[],[f268])).
% 1.90/0.62  fof(f268,plain,(
% 1.90/0.62    spl4_17 <=> k2_relat_1(sK2) = k1_relat_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.90/0.62  fof(f915,plain,(
% 1.90/0.62    ~spl4_16 | ~spl4_18 | ~spl4_5 | spl4_87 | ~spl4_59),
% 1.90/0.62    inference(avatar_split_clause,[],[f682,f606,f911,f152,f272,f264])).
% 1.90/0.62  fof(f264,plain,(
% 1.90/0.62    spl4_16 <=> v1_relat_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.90/0.62  fof(f272,plain,(
% 1.90/0.62    spl4_18 <=> v2_funct_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.90/0.62  fof(f152,plain,(
% 1.90/0.62    spl4_5 <=> v1_funct_1(sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.90/0.62  fof(f606,plain,(
% 1.90/0.62    spl4_59 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.90/0.62  fof(f682,plain,(
% 1.90/0.62    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_59),
% 1.90/0.62    inference(superposition,[],[f608,f89])).
% 1.90/0.62  fof(f89,plain,(
% 1.90/0.62    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f61,f55])).
% 1.90/0.62  fof(f61,plain,(
% 1.90/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f22])).
% 1.90/0.62  fof(f22,plain,(
% 1.90/0.62    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(flattening,[],[f21])).
% 1.90/0.62  fof(f21,plain,(
% 1.90/0.62    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.90/0.62    inference(ennf_transformation,[],[f3])).
% 1.90/0.62  fof(f3,axiom,(
% 1.90/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 1.90/0.62  fof(f608,plain,(
% 1.90/0.62    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_59),
% 1.90/0.62    inference(avatar_component_clause,[],[f606])).
% 1.90/0.62  fof(f909,plain,(
% 1.90/0.62    spl4_85),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f906])).
% 1.90/0.62  fof(f906,plain,(
% 1.90/0.62    $false | spl4_85),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f84,f900])).
% 1.90/0.62  fof(f900,plain,(
% 1.90/0.62    ~v2_funct_1(k6_partfun1(sK0)) | spl4_85),
% 1.90/0.62    inference(avatar_component_clause,[],[f898])).
% 1.90/0.62  fof(f898,plain,(
% 1.90/0.62    spl4_85 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 1.90/0.62  fof(f84,plain,(
% 1.90/0.62    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f58,f55])).
% 1.90/0.62  fof(f58,plain,(
% 1.90/0.62    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f2])).
% 1.90/0.62  fof(f2,axiom,(
% 1.90/0.62    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.90/0.62  fof(f901,plain,(
% 1.90/0.62    ~spl4_43 | ~spl4_4 | ~spl4_5 | spl4_58 | spl4_18 | ~spl4_85 | ~spl4_2 | ~spl4_63),
% 1.90/0.62    inference(avatar_split_clause,[],[f894,f668,f132,f898,f272,f601,f152,f148,f450])).
% 1.90/0.62  fof(f450,plain,(
% 1.90/0.62    spl4_43 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.90/0.62  fof(f148,plain,(
% 1.90/0.62    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.90/0.62  fof(f601,plain,(
% 1.90/0.62    spl4_58 <=> k1_xboole_0 = sK0),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.90/0.62  fof(f132,plain,(
% 1.90/0.62    spl4_2 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.90/0.62  fof(f668,plain,(
% 1.90/0.62    spl4_63 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 1.90/0.62  fof(f894,plain,(
% 1.90/0.62    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_2 | ~spl4_63)),
% 1.90/0.62    inference(superposition,[],[f669,f134])).
% 1.90/0.62  fof(f134,plain,(
% 1.90/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_2),
% 1.90/0.62    inference(avatar_component_clause,[],[f132])).
% 1.90/0.62  fof(f669,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_63),
% 1.90/0.62    inference(avatar_component_clause,[],[f668])).
% 1.90/0.62  fof(f763,plain,(
% 1.90/0.62    spl4_20 | ~spl4_61),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f762])).
% 1.90/0.62  fof(f762,plain,(
% 1.90/0.62    $false | (spl4_20 | ~spl4_61)),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f759])).
% 1.90/0.62  fof(f759,plain,(
% 1.90/0.62    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_20 | ~spl4_61)),
% 1.90/0.62    inference(superposition,[],[f282,f656])).
% 1.90/0.62  fof(f282,plain,(
% 1.90/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_20),
% 1.90/0.62    inference(avatar_component_clause,[],[f280])).
% 1.90/0.62  fof(f280,plain,(
% 1.90/0.62    spl4_20 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.90/0.62  fof(f756,plain,(
% 1.90/0.62    ~spl4_42 | ~spl4_74),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f754])).
% 1.90/0.62  fof(f754,plain,(
% 1.90/0.62    $false | (~spl4_42 | ~spl4_74)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f102,f448,f104,f746])).
% 1.90/0.62  fof(f746,plain,(
% 1.90/0.62    ( ! [X0] : (~v5_relat_1(k6_partfun1(sK0),X0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0)) ) | ~spl4_74),
% 1.90/0.62    inference(avatar_component_clause,[],[f745])).
% 1.90/0.62  fof(f745,plain,(
% 1.90/0.62    spl4_74 <=> ! [X0] : (~v5_relat_1(k6_partfun1(sK0),X0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 1.90/0.62  fof(f104,plain,(
% 1.90/0.62    ( ! [X0] : (v5_relat_1(k6_partfun1(X0),X0)) )),
% 1.90/0.62    inference(resolution,[],[f68,f83])).
% 1.90/0.62  fof(f83,plain,(
% 1.90/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.90/0.62    inference(definition_unfolding,[],[f56,f55])).
% 1.90/0.62  fof(f56,plain,(
% 1.90/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f8])).
% 1.90/0.62  fof(f8,axiom,(
% 1.90/0.62    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.90/0.62  fof(f68,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f28])).
% 1.90/0.62  fof(f28,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(ennf_transformation,[],[f6])).
% 1.90/0.62  fof(f6,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.90/0.62  fof(f448,plain,(
% 1.90/0.62    v2_funct_2(sK3,sK0) | ~spl4_42),
% 1.90/0.62    inference(avatar_component_clause,[],[f446])).
% 1.90/0.62  fof(f446,plain,(
% 1.90/0.62    spl4_42 <=> v2_funct_2(sK3,sK0)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.90/0.62  fof(f102,plain,(
% 1.90/0.62    v5_relat_1(sK3,sK0)),
% 1.90/0.62    inference(resolution,[],[f68,f45])).
% 1.90/0.62  fof(f45,plain,(
% 1.90/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f747,plain,(
% 1.90/0.62    ~spl4_16 | spl4_74 | spl4_30),
% 1.90/0.62    inference(avatar_split_clause,[],[f743,f356,f745,f264])).
% 1.90/0.62  fof(f356,plain,(
% 1.90/0.62    spl4_30 <=> v5_relat_1(k6_partfun1(sK0),k2_relat_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 1.90/0.62  fof(f743,plain,(
% 1.90/0.62    ( ! [X0] : (~v5_relat_1(k6_partfun1(sK0),X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | ~v2_funct_2(sK3,X0)) ) | spl4_30),
% 1.90/0.62    inference(superposition,[],[f358,f65])).
% 1.90/0.62  fof(f65,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v2_funct_2(X1,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f26])).
% 1.90/0.62  fof(f26,plain,(
% 1.90/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.90/0.62    inference(flattening,[],[f25])).
% 1.90/0.62  fof(f25,plain,(
% 1.90/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.90/0.62    inference(ennf_transformation,[],[f9])).
% 1.90/0.62  fof(f9,axiom,(
% 1.90/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.90/0.62  fof(f358,plain,(
% 1.90/0.62    ~v5_relat_1(k6_partfun1(sK0),k2_relat_1(sK3)) | spl4_30),
% 1.90/0.62    inference(avatar_component_clause,[],[f356])).
% 1.90/0.62  fof(f737,plain,(
% 1.90/0.62    spl4_61 | ~spl4_29 | ~spl4_30 | ~spl4_28),
% 1.90/0.62    inference(avatar_split_clause,[],[f734,f348,f356,f352,f654])).
% 1.90/0.62  fof(f352,plain,(
% 1.90/0.62    spl4_29 <=> v1_relat_1(k6_partfun1(sK0))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.90/0.62  fof(f348,plain,(
% 1.90/0.62    spl4_28 <=> v2_funct_2(k6_partfun1(sK0),k2_relat_1(sK3))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.90/0.62  fof(f734,plain,(
% 1.90/0.62    ~v5_relat_1(k6_partfun1(sK0),k2_relat_1(sK3)) | ~v1_relat_1(k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3) | ~spl4_28),
% 1.90/0.62    inference(resolution,[],[f350,f110])).
% 1.90/0.62  fof(f110,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v2_funct_2(k6_partfun1(X0),X1) | ~v5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0)) | X0 = X1) )),
% 1.90/0.62    inference(superposition,[],[f65,f86])).
% 1.90/0.62  fof(f350,plain,(
% 1.90/0.62    v2_funct_2(k6_partfun1(sK0),k2_relat_1(sK3)) | ~spl4_28),
% 1.90/0.62    inference(avatar_component_clause,[],[f348])).
% 1.90/0.62  fof(f733,plain,(
% 1.90/0.62    ~spl4_32 | ~spl4_39 | ~spl4_42 | ~spl4_65),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f730])).
% 1.90/0.62  fof(f730,plain,(
% 1.90/0.62    $false | (~spl4_32 | ~spl4_39 | ~spl4_42 | ~spl4_65)),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f102,f448,f482,f678])).
% 1.90/0.62  fof(f678,plain,(
% 1.90/0.62    ( ! [X0] : (~v2_funct_2(k6_partfun1(sK0),X0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0)) ) | ~spl4_65),
% 1.90/0.62    inference(avatar_component_clause,[],[f677])).
% 1.90/0.62  fof(f677,plain,(
% 1.90/0.62    spl4_65 <=> ! [X0] : (~v2_funct_2(k6_partfun1(sK0),X0) | ~v2_funct_2(sK3,X0) | ~v5_relat_1(sK3,X0))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 1.90/0.62  fof(f482,plain,(
% 1.90/0.62    v2_funct_2(k6_partfun1(sK0),sK0) | (~spl4_32 | ~spl4_39)),
% 1.90/0.62    inference(forward_demodulation,[],[f423,f418])).
% 1.90/0.62  fof(f423,plain,(
% 1.90/0.62    v2_funct_2(k6_partfun1(sK0),k1_relat_1(sK2)) | ~spl4_39),
% 1.90/0.62    inference(avatar_component_clause,[],[f421])).
% 1.90/0.62  fof(f421,plain,(
% 1.90/0.62    spl4_39 <=> v2_funct_2(k6_partfun1(sK0),k1_relat_1(sK2))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.90/0.62  fof(f709,plain,(
% 1.90/0.62    spl4_66 | ~spl4_67 | ~spl4_68 | ~spl4_69 | ~spl4_5 | ~spl4_16 | ~spl4_70 | ~spl4_71 | ~spl4_59),
% 1.90/0.62    inference(avatar_split_clause,[],[f684,f606,f706,f702,f264,f152,f698,f694,f690,f686])).
% 1.90/0.62  fof(f684,plain,(
% 1.90/0.62    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_59),
% 1.90/0.62    inference(superposition,[],[f90,f608])).
% 1.90/0.62  fof(f90,plain,(
% 1.90/0.62    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.90/0.62    inference(definition_unfolding,[],[f63,f55])).
% 1.90/0.62  fof(f63,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 1.90/0.62    inference(cnf_transformation,[],[f24])).
% 1.90/0.62  fof(f24,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.90/0.62    inference(flattening,[],[f23])).
% 1.90/0.62  fof(f23,plain,(
% 1.90/0.62    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.90/0.62    inference(ennf_transformation,[],[f4])).
% 1.90/0.62  fof(f4,axiom,(
% 1.90/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.90/0.62  fof(f679,plain,(
% 1.90/0.62    ~spl4_16 | spl4_65 | spl4_28),
% 1.90/0.62    inference(avatar_split_clause,[],[f675,f348,f677,f264])).
% 1.90/0.62  fof(f675,plain,(
% 1.90/0.62    ( ! [X0] : (~v2_funct_2(k6_partfun1(sK0),X0) | ~v5_relat_1(sK3,X0) | ~v1_relat_1(sK3) | ~v2_funct_2(sK3,X0)) ) | spl4_28),
% 1.90/0.62    inference(superposition,[],[f349,f65])).
% 1.90/0.62  fof(f349,plain,(
% 1.90/0.62    ~v2_funct_2(k6_partfun1(sK0),k2_relat_1(sK3)) | spl4_28),
% 1.90/0.62    inference(avatar_component_clause,[],[f348])).
% 1.90/0.62  fof(f670,plain,(
% 1.90/0.62    ~spl4_3 | spl4_63 | ~spl4_6 | ~spl4_14),
% 1.90/0.62    inference(avatar_split_clause,[],[f666,f234,f156,f668,f144])).
% 1.90/0.62  fof(f144,plain,(
% 1.90/0.62    spl4_3 <=> v1_funct_1(sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.90/0.62  fof(f156,plain,(
% 1.90/0.62    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.90/0.62  fof(f234,plain,(
% 1.90/0.62    spl4_14 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.90/0.62  fof(f666,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f663])).
% 1.90/0.62  fof(f663,plain,(
% 1.90/0.62    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.90/0.62    inference(superposition,[],[f77,f46])).
% 1.90/0.62  fof(f46,plain,(
% 1.90/0.62    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f77,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f36])).
% 1.90/0.62  fof(f36,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.90/0.62    inference(flattening,[],[f35])).
% 1.90/0.62  fof(f35,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.90/0.62    inference(ennf_transformation,[],[f15])).
% 1.90/0.62  fof(f15,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.90/0.62  fof(f642,plain,(
% 1.90/0.62    ~spl4_58),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f623])).
% 1.90/0.62  fof(f623,plain,(
% 1.90/0.62    $false | ~spl4_58),
% 1.90/0.62    inference(subsumption_resolution,[],[f49,f603])).
% 1.90/0.62  fof(f603,plain,(
% 1.90/0.62    k1_xboole_0 = sK0 | ~spl4_58),
% 1.90/0.62    inference(avatar_component_clause,[],[f601])).
% 1.90/0.62  fof(f49,plain,(
% 1.90/0.62    k1_xboole_0 != sK0),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f609,plain,(
% 1.90/0.62    spl4_59 | spl4_58 | ~spl4_18 | ~spl4_5 | ~spl4_4 | ~spl4_43 | ~spl4_56),
% 1.90/0.62    inference(avatar_split_clause,[],[f594,f570,f450,f148,f152,f272,f601,f606])).
% 1.90/0.62  fof(f570,plain,(
% 1.90/0.62    spl4_56 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.90/0.62  fof(f594,plain,(
% 1.90/0.62    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_56),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f593])).
% 1.90/0.62  fof(f593,plain,(
% 1.90/0.62    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_56),
% 1.90/0.62    inference(superposition,[],[f69,f572])).
% 1.90/0.62  fof(f572,plain,(
% 1.90/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_56),
% 1.90/0.62    inference(avatar_component_clause,[],[f570])).
% 1.90/0.62  fof(f69,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f30])).
% 1.90/0.62  fof(f30,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f29])).
% 1.90/0.62  fof(f29,plain,(
% 1.90/0.62    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f16])).
% 1.90/0.62  fof(f16,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.90/0.62  fof(f573,plain,(
% 1.90/0.62    spl4_56 | ~spl4_5 | ~spl4_6 | ~spl4_14 | ~spl4_3 | ~spl4_4 | ~spl4_43),
% 1.90/0.62    inference(avatar_split_clause,[],[f563,f450,f148,f144,f234,f156,f152,f570])).
% 1.90/0.62  fof(f563,plain,(
% 1.90/0.62    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.90/0.62    inference(resolution,[],[f71,f47])).
% 1.90/0.62  fof(f47,plain,(
% 1.90/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f71,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.90/0.62    inference(cnf_transformation,[],[f32])).
% 1.90/0.62  fof(f32,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f31])).
% 1.90/0.62  fof(f31,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f13])).
% 1.90/0.62  fof(f13,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.90/0.62  fof(f493,plain,(
% 1.90/0.62    ~spl4_19 | ~spl4_13 | ~spl4_3 | spl4_47 | ~spl4_22),
% 1.90/0.62    inference(avatar_split_clause,[],[f486,f296,f489,f144,f230,f276])).
% 1.90/0.62  fof(f276,plain,(
% 1.90/0.62    spl4_19 <=> v1_relat_1(sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.90/0.62  fof(f230,plain,(
% 1.90/0.62    spl4_13 <=> v2_funct_1(sK2)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.90/0.62  fof(f296,plain,(
% 1.90/0.62    spl4_22 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.90/0.62  fof(f486,plain,(
% 1.90/0.62    k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_22),
% 1.90/0.62    inference(superposition,[],[f88,f298])).
% 1.90/0.62  fof(f298,plain,(
% 1.90/0.62    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) | ~spl4_22),
% 1.90/0.62    inference(avatar_component_clause,[],[f296])).
% 1.90/0.62  fof(f88,plain,(
% 1.90/0.62    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.90/0.62    inference(definition_unfolding,[],[f62,f55])).
% 1.90/0.62  fof(f62,plain,(
% 1.90/0.62    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 1.90/0.62    inference(cnf_transformation,[],[f22])).
% 1.90/0.62  fof(f466,plain,(
% 1.90/0.62    spl4_43),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f465])).
% 1.90/0.62  fof(f465,plain,(
% 1.90/0.62    $false | spl4_43),
% 1.90/0.62    inference(subsumption_resolution,[],[f44,f452])).
% 1.90/0.62  fof(f452,plain,(
% 1.90/0.62    ~v1_funct_2(sK3,sK1,sK0) | spl4_43),
% 1.90/0.62    inference(avatar_component_clause,[],[f450])).
% 1.90/0.62  fof(f44,plain,(
% 1.90/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f453,plain,(
% 1.90/0.62    spl4_42 | ~spl4_3 | ~spl4_4 | ~spl4_43 | ~spl4_5 | ~spl4_6 | ~spl4_14),
% 1.90/0.62    inference(avatar_split_clause,[],[f440,f234,f156,f152,f450,f148,f144,f446])).
% 1.90/0.62  fof(f440,plain,(
% 1.90/0.62    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | v2_funct_2(sK3,sK0)),
% 1.90/0.62    inference(resolution,[],[f73,f47])).
% 1.90/0.62  fof(f73,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | v2_funct_2(X3,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f34])).
% 1.90/0.62  fof(f34,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.90/0.62    inference(flattening,[],[f33])).
% 1.90/0.62  fof(f33,plain,(
% 1.90/0.62    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.90/0.62    inference(ennf_transformation,[],[f14])).
% 1.90/0.62  fof(f14,axiom,(
% 1.90/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.90/0.62  fof(f439,plain,(
% 1.90/0.62    spl4_29),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f435])).
% 1.90/0.62  fof(f435,plain,(
% 1.90/0.62    $false | spl4_29),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f83,f354,f66])).
% 1.90/0.62  fof(f354,plain,(
% 1.90/0.62    ~v1_relat_1(k6_partfun1(sK0)) | spl4_29),
% 1.90/0.62    inference(avatar_component_clause,[],[f352])).
% 1.90/0.62  fof(f429,plain,(
% 1.90/0.62    ~spl4_29 | spl4_39 | ~spl4_32),
% 1.90/0.62    inference(avatar_split_clause,[],[f415,f375,f421,f352])).
% 1.90/0.62  fof(f415,plain,(
% 1.90/0.62    v2_funct_2(k6_partfun1(sK0),k1_relat_1(sK2)) | ~v1_relat_1(k6_partfun1(sK0)) | ~spl4_32),
% 1.90/0.62    inference(superposition,[],[f109,f377])).
% 1.90/0.62  fof(f109,plain,(
% 1.90/0.62    ( ! [X0] : (v2_funct_2(k6_partfun1(X0),X0) | ~v1_relat_1(k6_partfun1(X0))) )),
% 1.90/0.62    inference(resolution,[],[f105,f104])).
% 1.90/0.62  fof(f105,plain,(
% 1.90/0.62    ( ! [X0] : (~v5_relat_1(k6_partfun1(X0),X0) | ~v1_relat_1(k6_partfun1(X0)) | v2_funct_2(k6_partfun1(X0),X0)) )),
% 1.90/0.62    inference(superposition,[],[f91,f86])).
% 1.90/0.62  fof(f91,plain,(
% 1.90/0.62    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 1.90/0.62    inference(equality_resolution,[],[f64])).
% 1.90/0.62  fof(f64,plain,(
% 1.90/0.62    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f26])).
% 1.90/0.62  fof(f379,plain,(
% 1.90/0.62    ~spl4_19 | ~spl4_13 | ~spl4_3 | spl4_32 | ~spl4_11),
% 1.90/0.62    inference(avatar_split_clause,[],[f372,f222,f375,f144,f230,f276])).
% 1.90/0.62  fof(f222,plain,(
% 1.90/0.62    spl4_11 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.90/0.62  fof(f372,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_11),
% 1.90/0.62    inference(superposition,[],[f89,f224])).
% 1.90/0.62  fof(f224,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_11),
% 1.90/0.62    inference(avatar_component_clause,[],[f222])).
% 1.90/0.62  fof(f303,plain,(
% 1.90/0.62    spl4_19),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f300])).
% 1.90/0.62  fof(f300,plain,(
% 1.90/0.62    $false | spl4_19),
% 1.90/0.62    inference(subsumption_resolution,[],[f97,f278])).
% 1.90/0.62  fof(f278,plain,(
% 1.90/0.62    ~v1_relat_1(sK2) | spl4_19),
% 1.90/0.62    inference(avatar_component_clause,[],[f276])).
% 1.90/0.62  fof(f299,plain,(
% 1.90/0.62    spl4_22 | spl4_12 | ~spl4_13 | ~spl4_3 | ~spl4_6 | ~spl4_14),
% 1.90/0.62    inference(avatar_split_clause,[],[f294,f234,f156,f144,f230,f226,f296])).
% 1.90/0.62  fof(f226,plain,(
% 1.90/0.62    spl4_12 <=> k1_xboole_0 = sK1),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.90/0.62  fof(f294,plain,(
% 1.90/0.62    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f293])).
% 1.90/0.62  fof(f293,plain,(
% 1.90/0.62    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.90/0.62    inference(superposition,[],[f70,f46])).
% 1.90/0.62  fof(f70,plain,(
% 1.90/0.62    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f30])).
% 1.90/0.62  fof(f287,plain,(
% 1.90/0.62    spl4_16),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f284])).
% 1.90/0.62  fof(f284,plain,(
% 1.90/0.62    $false | spl4_16),
% 1.90/0.62    inference(subsumption_resolution,[],[f96,f266])).
% 1.90/0.62  fof(f266,plain,(
% 1.90/0.62    ~v1_relat_1(sK3) | spl4_16),
% 1.90/0.62    inference(avatar_component_clause,[],[f264])).
% 1.90/0.62  fof(f96,plain,(
% 1.90/0.62    v1_relat_1(sK3)),
% 1.90/0.62    inference(resolution,[],[f66,f45])).
% 1.90/0.62  fof(f283,plain,(
% 1.90/0.62    spl4_15 | ~spl4_16 | ~spl4_17 | ~spl4_18 | ~spl4_3 | ~spl4_19 | ~spl4_5 | ~spl4_20 | ~spl4_9),
% 1.90/0.62    inference(avatar_split_clause,[],[f258,f203,f280,f152,f276,f144,f272,f268,f264,f260])).
% 1.90/0.62  fof(f203,plain,(
% 1.90/0.62    spl4_9 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.90/0.62  fof(f258,plain,(
% 1.90/0.62    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_9),
% 1.90/0.62    inference(superposition,[],[f90,f205])).
% 1.90/0.62  fof(f205,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_9),
% 1.90/0.62    inference(avatar_component_clause,[],[f203])).
% 1.90/0.62  fof(f255,plain,(
% 1.90/0.62    ~spl4_12),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f242])).
% 1.90/0.62  fof(f242,plain,(
% 1.90/0.62    $false | ~spl4_12),
% 1.90/0.62    inference(subsumption_resolution,[],[f50,f228])).
% 1.90/0.62  fof(f228,plain,(
% 1.90/0.62    k1_xboole_0 = sK1 | ~spl4_12),
% 1.90/0.62    inference(avatar_component_clause,[],[f226])).
% 1.90/0.62  fof(f50,plain,(
% 1.90/0.62    k1_xboole_0 != sK1),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f241,plain,(
% 1.90/0.62    spl4_14),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f240])).
% 1.90/0.62  fof(f240,plain,(
% 1.90/0.62    $false | spl4_14),
% 1.90/0.62    inference(subsumption_resolution,[],[f53,f236])).
% 1.90/0.62  fof(f236,plain,(
% 1.90/0.62    ~v1_funct_2(sK2,sK0,sK1) | spl4_14),
% 1.90/0.62    inference(avatar_component_clause,[],[f234])).
% 1.90/0.62  fof(f53,plain,(
% 1.90/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f239,plain,(
% 1.90/0.62    spl4_13),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f238])).
% 1.90/0.62  fof(f238,plain,(
% 1.90/0.62    $false | spl4_13),
% 1.90/0.62    inference(subsumption_resolution,[],[f48,f232])).
% 1.90/0.62  fof(f232,plain,(
% 1.90/0.62    ~v2_funct_1(sK2) | spl4_13),
% 1.90/0.62    inference(avatar_component_clause,[],[f230])).
% 1.90/0.62  fof(f237,plain,(
% 1.90/0.62    spl4_11 | spl4_12 | ~spl4_13 | ~spl4_3 | ~spl4_6 | ~spl4_14),
% 1.90/0.62    inference(avatar_split_clause,[],[f220,f234,f156,f144,f230,f226,f222])).
% 1.90/0.62  fof(f220,plain,(
% 1.90/0.62    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.62    inference(trivial_inequality_removal,[],[f219])).
% 1.90/0.62  fof(f219,plain,(
% 1.90/0.62    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.90/0.62    inference(superposition,[],[f69,f46])).
% 1.90/0.62  fof(f213,plain,(
% 1.90/0.62    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_9 | ~spl4_2),
% 1.90/0.62    inference(avatar_split_clause,[],[f210,f132,f203,f156,f152,f148,f144])).
% 1.90/0.62  fof(f210,plain,(
% 1.90/0.62    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_2),
% 1.90/0.62    inference(superposition,[],[f80,f134])).
% 1.90/0.62  fof(f80,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f40])).
% 1.90/0.62  fof(f40,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.90/0.62    inference(flattening,[],[f39])).
% 1.90/0.62  fof(f39,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.90/0.62    inference(ennf_transformation,[],[f11])).
% 1.90/0.62  fof(f11,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.90/0.62  fof(f194,plain,(
% 1.90/0.62    spl4_6),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f193])).
% 1.90/0.62  fof(f193,plain,(
% 1.90/0.62    $false | spl4_6),
% 1.90/0.62    inference(subsumption_resolution,[],[f54,f158])).
% 1.90/0.62  fof(f158,plain,(
% 1.90/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_6),
% 1.90/0.62    inference(avatar_component_clause,[],[f156])).
% 1.90/0.62  fof(f186,plain,(
% 1.90/0.62    spl4_5),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f185])).
% 1.90/0.62  fof(f185,plain,(
% 1.90/0.62    $false | spl4_5),
% 1.90/0.62    inference(subsumption_resolution,[],[f43,f154])).
% 1.90/0.62  fof(f154,plain,(
% 1.90/0.62    ~v1_funct_1(sK3) | spl4_5),
% 1.90/0.62    inference(avatar_component_clause,[],[f152])).
% 1.90/0.62  fof(f43,plain,(
% 1.90/0.62    v1_funct_1(sK3)),
% 1.90/0.62    inference(cnf_transformation,[],[f20])).
% 1.90/0.62  fof(f184,plain,(
% 1.90/0.62    spl4_4),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f183])).
% 1.90/0.62  fof(f183,plain,(
% 1.90/0.62    $false | spl4_4),
% 1.90/0.62    inference(subsumption_resolution,[],[f45,f150])).
% 1.90/0.62  fof(f150,plain,(
% 1.90/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_4),
% 1.90/0.62    inference(avatar_component_clause,[],[f148])).
% 1.90/0.62  fof(f182,plain,(
% 1.90/0.62    spl4_3),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f181])).
% 1.90/0.62  fof(f181,plain,(
% 1.90/0.62    $false | spl4_3),
% 1.90/0.62    inference(subsumption_resolution,[],[f52,f146])).
% 1.90/0.62  fof(f146,plain,(
% 1.90/0.62    ~v1_funct_1(sK2) | spl4_3),
% 1.90/0.62    inference(avatar_component_clause,[],[f144])).
% 1.90/0.62  fof(f180,plain,(
% 1.90/0.62    spl4_1),
% 1.90/0.62    inference(avatar_contradiction_clause,[],[f169])).
% 1.90/0.62  fof(f169,plain,(
% 1.90/0.62    $false | spl4_1),
% 1.90/0.62    inference(unit_resulting_resolution,[],[f52,f43,f45,f54,f130,f82])).
% 1.90/0.62  fof(f82,plain,(
% 1.90/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f42])).
% 1.90/0.62  fof(f42,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.90/0.62    inference(flattening,[],[f41])).
% 1.90/0.62  fof(f41,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.90/0.62    inference(ennf_transformation,[],[f10])).
% 1.90/0.62  fof(f10,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.90/0.62  fof(f130,plain,(
% 1.90/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_1),
% 1.90/0.62    inference(avatar_component_clause,[],[f128])).
% 1.90/0.62  fof(f128,plain,(
% 1.90/0.62    spl4_1 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.90/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.90/0.62  fof(f135,plain,(
% 1.90/0.62    ~spl4_1 | spl4_2),
% 1.90/0.62    inference(avatar_split_clause,[],[f125,f132,f128])).
% 1.90/0.62  fof(f125,plain,(
% 1.90/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.90/0.62    inference(resolution,[],[f122,f47])).
% 1.90/0.62  fof(f122,plain,(
% 1.90/0.62    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.90/0.62    inference(resolution,[],[f79,f83])).
% 1.90/0.62  fof(f79,plain,(
% 1.90/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.90/0.62    inference(cnf_transformation,[],[f38])).
% 1.90/0.62  fof(f38,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.90/0.62    inference(flattening,[],[f37])).
% 1.90/0.62  fof(f37,plain,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.90/0.62    inference(ennf_transformation,[],[f7])).
% 1.90/0.62  fof(f7,axiom,(
% 1.90/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.90/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.90/0.62  % SZS output end Proof for theBenchmark
% 1.90/0.62  % (27783)------------------------------
% 1.90/0.62  % (27783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.62  % (27783)Termination reason: Refutation
% 1.90/0.62  
% 1.90/0.62  % (27783)Memory used [KB]: 7036
% 1.90/0.62  % (27783)Time elapsed: 0.183 s
% 1.90/0.62  % (27783)------------------------------
% 1.90/0.62  % (27783)------------------------------
% 2.03/0.63  % (27767)Success in time 0.269 s
%------------------------------------------------------------------------------
