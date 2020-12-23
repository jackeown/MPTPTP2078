%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:01 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 353 expanded)
%              Number of leaves         :   46 ( 136 expanded)
%              Depth                    :    8
%              Number of atoms          :  661 (1705 expanded)
%              Number of equality atoms :  133 ( 460 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1972,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f114,f118,f122,f143,f145,f151,f246,f322,f335,f337,f339,f362,f417,f429,f579,f586,f615,f616,f650,f673,f680,f690,f1473,f1481,f1810,f1924,f1965])).

fof(f1965,plain,(
    ~ spl4_228 ),
    inference(avatar_contradiction_clause,[],[f1943])).

fof(f1943,plain,
    ( $false
    | ~ spl4_228 ),
    inference(subsumption_resolution,[],[f54,f1923])).

fof(f1923,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_228 ),
    inference(avatar_component_clause,[],[f1921])).

fof(f1921,plain,
    ( spl4_228
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).

fof(f54,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f1924,plain,
    ( ~ spl4_1
    | ~ spl4_65
    | ~ spl4_29
    | spl4_228
    | ~ spl4_71
    | ~ spl4_75 ),
    inference(avatar_split_clause,[],[f1915,f704,f647,f1921,f306,f607,f98])).

fof(f98,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f607,plain,
    ( spl4_65
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f306,plain,
    ( spl4_29
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f647,plain,
    ( spl4_71
  <=> k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f704,plain,
    ( spl4_75
  <=> sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f1915,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_71
    | ~ spl4_75 ),
    inference(superposition,[],[f69,f1907])).

fof(f1907,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_71
    | ~ spl4_75 ),
    inference(forward_demodulation,[],[f649,f706])).

fof(f706,plain,
    ( sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_75 ),
    inference(avatar_component_clause,[],[f704])).

fof(f649,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f647])).

fof(f69,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f1810,plain,
    ( ~ spl4_70
    | spl4_75
    | ~ spl4_7
    | ~ spl4_41
    | ~ spl4_66 ),
    inference(avatar_split_clause,[],[f1809,f612,f427,f148,f704,f643])).

fof(f643,plain,
    ( spl4_70
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f148,plain,
    ( spl4_7
  <=> sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f427,plain,
    ( spl4_41
  <=> ! [X0] :
        ( k5_relat_1(k6_partfun1(sK0),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f612,plain,
    ( spl4_66
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f1809,plain,
    ( sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_7
    | ~ spl4_41
    | ~ spl4_66 ),
    inference(forward_demodulation,[],[f1804,f150])).

fof(f150,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f148])).

fof(f1804,plain,
    ( k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_41
    | ~ spl4_66 ),
    inference(superposition,[],[f428,f614])).

fof(f614,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_66 ),
    inference(avatar_component_clause,[],[f612])).

fof(f428,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_partfun1(sK0),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f427])).

fof(f1481,plain,(
    spl4_182 ),
    inference(avatar_contradiction_clause,[],[f1478])).

fof(f1478,plain,
    ( $false
    | spl4_182 ),
    inference(unit_resulting_resolution,[],[f86,f1472])).

fof(f1472,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_182 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f1470,plain,
    ( spl4_182
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f86,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1473,plain,
    ( ~ spl4_60
    | ~ spl4_28
    | ~ spl4_29
    | spl4_64
    | spl4_65
    | ~ spl4_182
    | ~ spl4_19
    | ~ spl4_72 ),
    inference(avatar_split_clause,[],[f1466,f688,f243,f1470,f607,f603,f306,f302,f576])).

fof(f576,plain,
    ( spl4_60
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f302,plain,
    ( spl4_28
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f603,plain,
    ( spl4_64
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f243,plain,
    ( spl4_19
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f688,plain,
    ( spl4_72
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f1466,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_19
    | ~ spl4_72 ),
    inference(superposition,[],[f689,f245])).

fof(f245,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f243])).

fof(f689,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_72 ),
    inference(avatar_component_clause,[],[f688])).

fof(f690,plain,
    ( ~ spl4_25
    | spl4_72
    | ~ spl4_5
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f686,f357,f135,f688,f285])).

fof(f285,plain,
    ( spl4_25
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f135,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f357,plain,
    ( spl4_34
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f686,plain,(
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
    inference(trivial_inequality_removal,[],[f681])).

fof(f681,plain,(
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
    inference(superposition,[],[f80,f49])).

fof(f49,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f680,plain,
    ( ~ spl4_1
    | spl4_70 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | ~ spl4_1
    | spl4_70 ),
    inference(unit_resulting_resolution,[],[f100,f46,f645,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f645,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_70 ),
    inference(avatar_component_clause,[],[f643])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f673,plain,(
    ~ spl4_64 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f52,f605])).

fof(f605,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f603])).

fof(f52,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f22])).

fof(f650,plain,
    ( ~ spl4_1
    | ~ spl4_65
    | ~ spl4_29
    | ~ spl4_70
    | spl4_71
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f618,f594,f647,f643,f306,f607,f98])).

fof(f594,plain,
    ( spl4_62
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f618,plain,
    ( k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_62 ),
    inference(superposition,[],[f129,f596])).

fof(f596,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f594])).

fof(f129,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f89,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f58])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f616,plain,
    ( ~ spl4_28
    | spl4_62
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f590,f572,f594,f302])).

fof(f572,plain,
    ( spl4_59
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f590,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_59 ),
    inference(superposition,[],[f73,f574])).

fof(f574,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f572])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f615,plain,
    ( spl4_66
    | spl4_64
    | ~ spl4_65
    | ~ spl4_29
    | ~ spl4_28
    | ~ spl4_60
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f591,f572,f576,f302,f306,f607,f603,f612])).

fof(f591,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_59 ),
    inference(trivial_inequality_removal,[],[f589])).

fof(f589,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_59 ),
    inference(superposition,[],[f74,f574])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f586,plain,(
    spl4_60 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl4_60 ),
    inference(subsumption_resolution,[],[f47,f578])).

fof(f578,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f576])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f579,plain,
    ( spl4_59
    | ~ spl4_29
    | ~ spl4_5
    | ~ spl4_34
    | ~ spl4_25
    | ~ spl4_28
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f567,f576,f302,f285,f357,f135,f306,f572])).

fof(f567,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f76,f50])).

fof(f50,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f429,plain,
    ( ~ spl4_3
    | ~ spl4_1
    | spl4_41
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f425,f402,f427,f98,f107])).

fof(f107,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f402,plain,
    ( spl4_38
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f425,plain,
    ( ! [X0] :
        ( k5_relat_1(k6_partfun1(sK0),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_38 ),
    inference(superposition,[],[f65,f404])).

fof(f404,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f402])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f417,plain,
    ( ~ spl4_25
    | ~ spl4_28
    | ~ spl4_29
    | ~ spl4_5
    | spl4_38
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f414,f243,f402,f135,f306,f302,f285])).

fof(f414,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f83,f245])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f362,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | spl4_34 ),
    inference(subsumption_resolution,[],[f56,f359])).

fof(f359,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_34 ),
    inference(avatar_component_clause,[],[f357])).

fof(f56,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f339,plain,(
    spl4_29 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl4_29 ),
    inference(subsumption_resolution,[],[f46,f308])).

fof(f308,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f306])).

fof(f337,plain,(
    spl4_28 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | spl4_28 ),
    inference(subsumption_resolution,[],[f48,f304])).

fof(f304,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f302])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f335,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl4_18 ),
    inference(unit_resulting_resolution,[],[f55,f46,f48,f57,f241,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f241,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl4_18
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f322,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl4_25 ),
    inference(subsumption_resolution,[],[f55,f287])).

fof(f287,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f285])).

fof(f246,plain,
    ( ~ spl4_18
    | spl4_19 ),
    inference(avatar_split_clause,[],[f236,f243,f239])).

fof(f236,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f178,f50])).

fof(f178,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f82,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f151,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f146,f139,f148,f107])).

fof(f139,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f146,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f88,f141])).

fof(f141,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f88,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f58])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f145,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f57,f137])).

fof(f137,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f143,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f133,f139,f135])).

fof(f133,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f49,f73])).

fof(f122,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f72,f113])).

fof(f113,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f72,f104])).

fof(f104,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f114,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f95,f111,f107])).

fof(f95,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f105,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f94,f102,f98])).

fof(f94,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (24514)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.50  % (24495)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (24491)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (24519)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (24492)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (24499)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (24504)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (24496)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (24490)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (24503)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (24509)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (24502)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (24498)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (24510)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (24518)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (24512)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (24497)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (24517)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (24513)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (24493)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (24494)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (24506)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (24506)Refutation not found, incomplete strategy% (24506)------------------------------
% 0.20/0.54  % (24506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24506)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24506)Memory used [KB]: 10746
% 0.20/0.54  % (24506)Time elapsed: 0.151 s
% 0.20/0.54  % (24506)------------------------------
% 0.20/0.54  % (24506)------------------------------
% 0.20/0.54  % (24505)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (24501)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (24515)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (24508)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.55  % (24507)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (24511)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (24500)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.56  % (24516)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.14/0.64  % (24503)Refutation found. Thanks to Tanya!
% 2.14/0.64  % SZS status Theorem for theBenchmark
% 2.21/0.64  % SZS output start Proof for theBenchmark
% 2.21/0.64  fof(f1972,plain,(
% 2.21/0.64    $false),
% 2.21/0.64    inference(avatar_sat_refutation,[],[f105,f114,f118,f122,f143,f145,f151,f246,f322,f335,f337,f339,f362,f417,f429,f579,f586,f615,f616,f650,f673,f680,f690,f1473,f1481,f1810,f1924,f1965])).
% 2.21/0.65  fof(f1965,plain,(
% 2.21/0.65    ~spl4_228),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f1943])).
% 2.21/0.65  fof(f1943,plain,(
% 2.21/0.65    $false | ~spl4_228),
% 2.21/0.65    inference(subsumption_resolution,[],[f54,f1923])).
% 2.21/0.65  fof(f1923,plain,(
% 2.21/0.65    sK3 = k2_funct_1(sK2) | ~spl4_228),
% 2.21/0.65    inference(avatar_component_clause,[],[f1921])).
% 2.21/0.65  fof(f1921,plain,(
% 2.21/0.65    spl4_228 <=> sK3 = k2_funct_1(sK2)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_228])])).
% 2.21/0.65  fof(f54,plain,(
% 2.21/0.65    sK3 != k2_funct_1(sK2)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f22,plain,(
% 2.21/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.21/0.65    inference(flattening,[],[f21])).
% 2.21/0.65  fof(f21,plain,(
% 2.21/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.21/0.65    inference(ennf_transformation,[],[f20])).
% 2.21/0.65  fof(f20,negated_conjecture,(
% 2.21/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.21/0.65    inference(negated_conjecture,[],[f19])).
% 2.21/0.65  fof(f19,conjecture,(
% 2.21/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.21/0.65  fof(f1924,plain,(
% 2.21/0.65    ~spl4_1 | ~spl4_65 | ~spl4_29 | spl4_228 | ~spl4_71 | ~spl4_75),
% 2.21/0.65    inference(avatar_split_clause,[],[f1915,f704,f647,f1921,f306,f607,f98])).
% 2.21/0.65  fof(f98,plain,(
% 2.21/0.65    spl4_1 <=> v1_relat_1(sK3)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.21/0.65  fof(f607,plain,(
% 2.21/0.65    spl4_65 <=> v2_funct_1(sK3)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 2.21/0.65  fof(f306,plain,(
% 2.21/0.65    spl4_29 <=> v1_funct_1(sK3)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.21/0.65  fof(f647,plain,(
% 2.21/0.65    spl4_71 <=> k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 2.21/0.65  fof(f704,plain,(
% 2.21/0.65    spl4_75 <=> sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 2.21/0.65  fof(f1915,plain,(
% 2.21/0.65    sK3 = k2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_71 | ~spl4_75)),
% 2.21/0.65    inference(superposition,[],[f69,f1907])).
% 2.21/0.65  fof(f1907,plain,(
% 2.21/0.65    sK2 = k2_funct_1(sK3) | (~spl4_71 | ~spl4_75)),
% 2.21/0.65    inference(forward_demodulation,[],[f649,f706])).
% 2.21/0.65  fof(f706,plain,(
% 2.21/0.65    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~spl4_75),
% 2.21/0.65    inference(avatar_component_clause,[],[f704])).
% 2.21/0.65  fof(f649,plain,(
% 2.21/0.65    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~spl4_71),
% 2.21/0.65    inference(avatar_component_clause,[],[f647])).
% 2.21/0.65  fof(f69,plain,(
% 2.21/0.65    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f30])).
% 2.21/0.65  fof(f30,plain,(
% 2.21/0.65    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(flattening,[],[f29])).
% 2.21/0.65  fof(f29,plain,(
% 2.21/0.65    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f9])).
% 2.21/0.65  fof(f9,axiom,(
% 2.21/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 2.21/0.65  fof(f1810,plain,(
% 2.21/0.65    ~spl4_70 | spl4_75 | ~spl4_7 | ~spl4_41 | ~spl4_66),
% 2.21/0.65    inference(avatar_split_clause,[],[f1809,f612,f427,f148,f704,f643])).
% 2.21/0.65  fof(f643,plain,(
% 2.21/0.65    spl4_70 <=> v1_relat_1(k2_funct_1(sK3))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).
% 2.21/0.65  fof(f148,plain,(
% 2.21/0.65    spl4_7 <=> sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.21/0.65  fof(f427,plain,(
% 2.21/0.65    spl4_41 <=> ! [X0] : (k5_relat_1(k6_partfun1(sK0),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0)) | ~v1_relat_1(X0))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 2.21/0.65  fof(f612,plain,(
% 2.21/0.65    spl4_66 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).
% 2.21/0.65  fof(f1809,plain,(
% 2.21/0.65    sK2 = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_7 | ~spl4_41 | ~spl4_66)),
% 2.21/0.65    inference(forward_demodulation,[],[f1804,f150])).
% 2.21/0.65  fof(f150,plain,(
% 2.21/0.65    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~spl4_7),
% 2.21/0.65    inference(avatar_component_clause,[],[f148])).
% 2.21/0.65  fof(f1804,plain,(
% 2.21/0.65    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_41 | ~spl4_66)),
% 2.21/0.65    inference(superposition,[],[f428,f614])).
% 2.21/0.65  fof(f614,plain,(
% 2.21/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_66),
% 2.21/0.65    inference(avatar_component_clause,[],[f612])).
% 2.21/0.65  fof(f428,plain,(
% 2.21/0.65    ( ! [X0] : (k5_relat_1(k6_partfun1(sK0),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0)) | ~v1_relat_1(X0)) ) | ~spl4_41),
% 2.21/0.65    inference(avatar_component_clause,[],[f427])).
% 2.21/0.65  fof(f1481,plain,(
% 2.21/0.65    spl4_182),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f1478])).
% 2.21/0.65  fof(f1478,plain,(
% 2.21/0.65    $false | spl4_182),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f86,f1472])).
% 2.21/0.65  fof(f1472,plain,(
% 2.21/0.65    ~v2_funct_1(k6_partfun1(sK0)) | spl4_182),
% 2.21/0.65    inference(avatar_component_clause,[],[f1470])).
% 2.21/0.65  fof(f1470,plain,(
% 2.21/0.65    spl4_182 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).
% 2.21/0.65  fof(f86,plain,(
% 2.21/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.21/0.65    inference(definition_unfolding,[],[f60,f58])).
% 2.21/0.65  fof(f58,plain,(
% 2.21/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f15])).
% 2.21/0.65  fof(f15,axiom,(
% 2.21/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.21/0.65  fof(f60,plain,(
% 2.21/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f7])).
% 2.21/0.65  fof(f7,axiom,(
% 2.21/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.21/0.65  fof(f1473,plain,(
% 2.21/0.65    ~spl4_60 | ~spl4_28 | ~spl4_29 | spl4_64 | spl4_65 | ~spl4_182 | ~spl4_19 | ~spl4_72),
% 2.21/0.65    inference(avatar_split_clause,[],[f1466,f688,f243,f1470,f607,f603,f306,f302,f576])).
% 2.21/0.65  fof(f576,plain,(
% 2.21/0.65    spl4_60 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 2.21/0.65  fof(f302,plain,(
% 2.21/0.65    spl4_28 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 2.21/0.65  fof(f603,plain,(
% 2.21/0.65    spl4_64 <=> k1_xboole_0 = sK0),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 2.21/0.65  fof(f243,plain,(
% 2.21/0.65    spl4_19 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.21/0.65  fof(f688,plain,(
% 2.21/0.65    spl4_72 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 2.21/0.65  fof(f1466,plain,(
% 2.21/0.65    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_19 | ~spl4_72)),
% 2.21/0.65    inference(superposition,[],[f689,f245])).
% 2.21/0.65  fof(f245,plain,(
% 2.21/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_19),
% 2.21/0.65    inference(avatar_component_clause,[],[f243])).
% 2.21/0.65  fof(f689,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_72),
% 2.21/0.65    inference(avatar_component_clause,[],[f688])).
% 2.21/0.65  fof(f690,plain,(
% 2.21/0.65    ~spl4_25 | spl4_72 | ~spl4_5 | ~spl4_34),
% 2.21/0.65    inference(avatar_split_clause,[],[f686,f357,f135,f688,f285])).
% 2.21/0.65  fof(f285,plain,(
% 2.21/0.65    spl4_25 <=> v1_funct_1(sK2)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.21/0.65  fof(f135,plain,(
% 2.21/0.65    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.21/0.65  fof(f357,plain,(
% 2.21/0.65    spl4_34 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 2.21/0.65  fof(f686,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.21/0.65    inference(trivial_inequality_removal,[],[f681])).
% 2.21/0.65  fof(f681,plain,(
% 2.21/0.65    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 2.21/0.65    inference(superposition,[],[f80,f49])).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f80,plain,(
% 2.21/0.65    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f39])).
% 2.21/0.65  fof(f39,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.21/0.65    inference(flattening,[],[f38])).
% 2.21/0.65  fof(f38,plain,(
% 2.21/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.21/0.65    inference(ennf_transformation,[],[f17])).
% 2.21/0.65  fof(f17,axiom,(
% 2.21/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.21/0.65  fof(f680,plain,(
% 2.21/0.65    ~spl4_1 | spl4_70),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f678])).
% 2.21/0.65  fof(f678,plain,(
% 2.21/0.65    $false | (~spl4_1 | spl4_70)),
% 2.21/0.65    inference(unit_resulting_resolution,[],[f100,f46,f645,f67])).
% 2.21/0.65  fof(f67,plain,(
% 2.21/0.65    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f28])).
% 2.21/0.65  fof(f28,plain,(
% 2.21/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(flattening,[],[f27])).
% 2.21/0.65  fof(f27,plain,(
% 2.21/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f6])).
% 2.21/0.65  fof(f6,axiom,(
% 2.21/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.21/0.65  fof(f645,plain,(
% 2.21/0.65    ~v1_relat_1(k2_funct_1(sK3)) | spl4_70),
% 2.21/0.65    inference(avatar_component_clause,[],[f643])).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    v1_funct_1(sK3)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f100,plain,(
% 2.21/0.65    v1_relat_1(sK3) | ~spl4_1),
% 2.21/0.65    inference(avatar_component_clause,[],[f98])).
% 2.21/0.65  fof(f673,plain,(
% 2.21/0.65    ~spl4_64),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f651])).
% 2.21/0.65  fof(f651,plain,(
% 2.21/0.65    $false | ~spl4_64),
% 2.21/0.65    inference(subsumption_resolution,[],[f52,f605])).
% 2.21/0.65  fof(f605,plain,(
% 2.21/0.65    k1_xboole_0 = sK0 | ~spl4_64),
% 2.21/0.65    inference(avatar_component_clause,[],[f603])).
% 2.21/0.65  fof(f52,plain,(
% 2.21/0.65    k1_xboole_0 != sK0),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f650,plain,(
% 2.21/0.65    ~spl4_1 | ~spl4_65 | ~spl4_29 | ~spl4_70 | spl4_71 | ~spl4_62),
% 2.21/0.65    inference(avatar_split_clause,[],[f618,f594,f647,f643,f306,f607,f98])).
% 2.21/0.65  fof(f594,plain,(
% 2.21/0.65    spl4_62 <=> sK0 = k2_relat_1(sK3)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 2.21/0.65  fof(f618,plain,(
% 2.21/0.65    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_62),
% 2.21/0.65    inference(superposition,[],[f129,f596])).
% 2.21/0.65  fof(f596,plain,(
% 2.21/0.65    sK0 = k2_relat_1(sK3) | ~spl4_62),
% 2.21/0.65    inference(avatar_component_clause,[],[f594])).
% 2.21/0.65  fof(f129,plain,(
% 2.21/0.65    ( ! [X0] : (k2_funct_1(X0) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(superposition,[],[f89,f70])).
% 2.21/0.65  fof(f70,plain,(
% 2.21/0.65    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f32])).
% 2.21/0.65  fof(f32,plain,(
% 2.21/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(flattening,[],[f31])).
% 2.21/0.65  fof(f31,plain,(
% 2.21/0.65    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.65    inference(ennf_transformation,[],[f8])).
% 2.21/0.65  fof(f8,axiom,(
% 2.21/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.21/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.21/0.65  fof(f89,plain,(
% 2.21/0.65    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.21/0.65    inference(definition_unfolding,[],[f64,f58])).
% 2.21/0.65  fof(f64,plain,(
% 2.21/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.21/0.65    inference(cnf_transformation,[],[f24])).
% 2.21/0.65  fof(f24,plain,(
% 2.21/0.65    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f4])).
% 2.21/0.66  fof(f4,axiom,(
% 2.21/0.66    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.21/0.66  fof(f616,plain,(
% 2.21/0.66    ~spl4_28 | spl4_62 | ~spl4_59),
% 2.21/0.66    inference(avatar_split_clause,[],[f590,f572,f594,f302])).
% 2.21/0.66  fof(f572,plain,(
% 2.21/0.66    spl4_59 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 2.21/0.66  fof(f590,plain,(
% 2.21/0.66    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_59),
% 2.21/0.66    inference(superposition,[],[f73,f574])).
% 2.21/0.66  fof(f574,plain,(
% 2.21/0.66    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_59),
% 2.21/0.66    inference(avatar_component_clause,[],[f572])).
% 2.21/0.66  fof(f73,plain,(
% 2.21/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/0.66    inference(cnf_transformation,[],[f33])).
% 2.21/0.66  fof(f33,plain,(
% 2.21/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.66    inference(ennf_transformation,[],[f10])).
% 2.21/0.66  fof(f10,axiom,(
% 2.21/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.21/0.66  fof(f615,plain,(
% 2.21/0.66    spl4_66 | spl4_64 | ~spl4_65 | ~spl4_29 | ~spl4_28 | ~spl4_60 | ~spl4_59),
% 2.21/0.66    inference(avatar_split_clause,[],[f591,f572,f576,f302,f306,f607,f603,f612])).
% 2.21/0.66  fof(f591,plain,(
% 2.21/0.66    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_59),
% 2.21/0.66    inference(trivial_inequality_removal,[],[f589])).
% 2.21/0.66  fof(f589,plain,(
% 2.21/0.66    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_59),
% 2.21/0.66    inference(superposition,[],[f74,f574])).
% 2.21/0.66  fof(f74,plain,(
% 2.21/0.66    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.21/0.66    inference(cnf_transformation,[],[f35])).
% 2.21/0.66  fof(f35,plain,(
% 2.21/0.66    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.21/0.66    inference(flattening,[],[f34])).
% 2.21/0.66  fof(f34,plain,(
% 2.21/0.66    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.21/0.66    inference(ennf_transformation,[],[f18])).
% 2.21/0.66  fof(f18,axiom,(
% 2.21/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.21/0.66  fof(f586,plain,(
% 2.21/0.66    spl4_60),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f585])).
% 2.21/0.66  fof(f585,plain,(
% 2.21/0.66    $false | spl4_60),
% 2.21/0.66    inference(subsumption_resolution,[],[f47,f578])).
% 2.21/0.66  fof(f578,plain,(
% 2.21/0.66    ~v1_funct_2(sK3,sK1,sK0) | spl4_60),
% 2.21/0.66    inference(avatar_component_clause,[],[f576])).
% 2.21/0.66  fof(f47,plain,(
% 2.21/0.66    v1_funct_2(sK3,sK1,sK0)),
% 2.21/0.66    inference(cnf_transformation,[],[f22])).
% 2.21/0.66  fof(f579,plain,(
% 2.21/0.66    spl4_59 | ~spl4_29 | ~spl4_5 | ~spl4_34 | ~spl4_25 | ~spl4_28 | ~spl4_60),
% 2.21/0.66    inference(avatar_split_clause,[],[f567,f576,f302,f285,f357,f135,f306,f572])).
% 2.21/0.66  fof(f567,plain,(
% 2.21/0.66    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 2.21/0.66    inference(resolution,[],[f76,f50])).
% 2.21/0.66  fof(f50,plain,(
% 2.21/0.66    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.21/0.66    inference(cnf_transformation,[],[f22])).
% 2.21/0.66  fof(f76,plain,(
% 2.21/0.66    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.21/0.66    inference(cnf_transformation,[],[f37])).
% 2.21/0.66  fof(f37,plain,(
% 2.21/0.66    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.21/0.66    inference(flattening,[],[f36])).
% 2.21/0.66  fof(f36,plain,(
% 2.21/0.66    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.21/0.66    inference(ennf_transformation,[],[f16])).
% 2.21/0.66  fof(f16,axiom,(
% 2.21/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.21/0.66  fof(f429,plain,(
% 2.21/0.66    ~spl4_3 | ~spl4_1 | spl4_41 | ~spl4_38),
% 2.21/0.66    inference(avatar_split_clause,[],[f425,f402,f427,f98,f107])).
% 2.21/0.66  fof(f107,plain,(
% 2.21/0.66    spl4_3 <=> v1_relat_1(sK2)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.21/0.66  fof(f402,plain,(
% 2.21/0.66    spl4_38 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 2.21/0.66  fof(f425,plain,(
% 2.21/0.66    ( ! [X0] : (k5_relat_1(k6_partfun1(sK0),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0)) | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) ) | ~spl4_38),
% 2.21/0.66    inference(superposition,[],[f65,f404])).
% 2.21/0.66  fof(f404,plain,(
% 2.21/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_38),
% 2.21/0.66    inference(avatar_component_clause,[],[f402])).
% 2.21/0.66  fof(f65,plain,(
% 2.21/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f25])).
% 2.21/0.66  fof(f25,plain,(
% 2.21/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/0.66    inference(ennf_transformation,[],[f3])).
% 2.21/0.66  fof(f3,axiom,(
% 2.21/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.21/0.66  fof(f417,plain,(
% 2.21/0.66    ~spl4_25 | ~spl4_28 | ~spl4_29 | ~spl4_5 | spl4_38 | ~spl4_19),
% 2.21/0.66    inference(avatar_split_clause,[],[f414,f243,f402,f135,f306,f302,f285])).
% 2.21/0.66  fof(f414,plain,(
% 2.21/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_19),
% 2.21/0.66    inference(superposition,[],[f83,f245])).
% 2.21/0.66  fof(f83,plain,(
% 2.21/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f43])).
% 2.21/0.66  fof(f43,plain,(
% 2.21/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.21/0.66    inference(flattening,[],[f42])).
% 2.21/0.66  fof(f42,plain,(
% 2.21/0.66    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.21/0.66    inference(ennf_transformation,[],[f14])).
% 2.21/0.66  fof(f14,axiom,(
% 2.21/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.21/0.66  fof(f362,plain,(
% 2.21/0.66    spl4_34),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f361])).
% 2.21/0.66  fof(f361,plain,(
% 2.21/0.66    $false | spl4_34),
% 2.21/0.66    inference(subsumption_resolution,[],[f56,f359])).
% 2.21/0.66  fof(f359,plain,(
% 2.21/0.66    ~v1_funct_2(sK2,sK0,sK1) | spl4_34),
% 2.21/0.66    inference(avatar_component_clause,[],[f357])).
% 2.21/0.66  fof(f56,plain,(
% 2.21/0.66    v1_funct_2(sK2,sK0,sK1)),
% 2.21/0.66    inference(cnf_transformation,[],[f22])).
% 2.21/0.66  fof(f339,plain,(
% 2.21/0.66    spl4_29),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f338])).
% 2.21/0.66  fof(f338,plain,(
% 2.21/0.66    $false | spl4_29),
% 2.21/0.66    inference(subsumption_resolution,[],[f46,f308])).
% 2.21/0.66  fof(f308,plain,(
% 2.21/0.66    ~v1_funct_1(sK3) | spl4_29),
% 2.21/0.66    inference(avatar_component_clause,[],[f306])).
% 2.21/0.66  fof(f337,plain,(
% 2.21/0.66    spl4_28),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f336])).
% 2.21/0.66  fof(f336,plain,(
% 2.21/0.66    $false | spl4_28),
% 2.21/0.66    inference(subsumption_resolution,[],[f48,f304])).
% 2.21/0.66  fof(f304,plain,(
% 2.21/0.66    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_28),
% 2.21/0.66    inference(avatar_component_clause,[],[f302])).
% 2.21/0.66  fof(f48,plain,(
% 2.21/0.66    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.66    inference(cnf_transformation,[],[f22])).
% 2.21/0.66  fof(f335,plain,(
% 2.21/0.66    spl4_18),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f326])).
% 2.21/0.66  fof(f326,plain,(
% 2.21/0.66    $false | spl4_18),
% 2.21/0.66    inference(unit_resulting_resolution,[],[f55,f46,f48,f57,f241,f85])).
% 2.21/0.66  fof(f85,plain,(
% 2.21/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f45])).
% 2.21/0.66  fof(f45,plain,(
% 2.21/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.21/0.66    inference(flattening,[],[f44])).
% 2.21/0.66  fof(f44,plain,(
% 2.21/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.21/0.66    inference(ennf_transformation,[],[f12])).
% 2.21/0.66  fof(f12,axiom,(
% 2.21/0.66    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.21/0.66  fof(f241,plain,(
% 2.21/0.66    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_18),
% 2.21/0.66    inference(avatar_component_clause,[],[f239])).
% 2.21/0.66  fof(f239,plain,(
% 2.21/0.66    spl4_18 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.21/0.66  fof(f57,plain,(
% 2.21/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.66    inference(cnf_transformation,[],[f22])).
% 2.21/0.66  fof(f55,plain,(
% 2.21/0.66    v1_funct_1(sK2)),
% 2.21/0.66    inference(cnf_transformation,[],[f22])).
% 2.21/0.66  fof(f322,plain,(
% 2.21/0.66    spl4_25),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f321])).
% 2.21/0.66  fof(f321,plain,(
% 2.21/0.66    $false | spl4_25),
% 2.21/0.66    inference(subsumption_resolution,[],[f55,f287])).
% 2.21/0.66  fof(f287,plain,(
% 2.21/0.66    ~v1_funct_1(sK2) | spl4_25),
% 2.21/0.66    inference(avatar_component_clause,[],[f285])).
% 2.21/0.66  fof(f246,plain,(
% 2.21/0.66    ~spl4_18 | spl4_19),
% 2.21/0.66    inference(avatar_split_clause,[],[f236,f243,f239])).
% 2.21/0.66  fof(f236,plain,(
% 2.21/0.66    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.21/0.66    inference(resolution,[],[f178,f50])).
% 2.21/0.66  fof(f178,plain,(
% 2.21/0.66    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.21/0.66    inference(resolution,[],[f82,f62])).
% 2.21/0.66  fof(f62,plain,(
% 2.21/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.21/0.66    inference(cnf_transformation,[],[f13])).
% 2.21/0.66  fof(f13,axiom,(
% 2.21/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.21/0.66  fof(f82,plain,(
% 2.21/0.66    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f41])).
% 2.21/0.66  fof(f41,plain,(
% 2.21/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.66    inference(flattening,[],[f40])).
% 2.21/0.66  fof(f40,plain,(
% 2.21/0.66    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.21/0.66    inference(ennf_transformation,[],[f11])).
% 2.21/0.66  fof(f11,axiom,(
% 2.21/0.66    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.21/0.66  fof(f151,plain,(
% 2.21/0.66    ~spl4_3 | spl4_7 | ~spl4_6),
% 2.21/0.66    inference(avatar_split_clause,[],[f146,f139,f148,f107])).
% 2.21/0.66  fof(f139,plain,(
% 2.21/0.66    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.21/0.66  fof(f146,plain,(
% 2.21/0.66    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~v1_relat_1(sK2) | ~spl4_6),
% 2.21/0.66    inference(superposition,[],[f88,f141])).
% 2.21/0.66  fof(f141,plain,(
% 2.21/0.66    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 2.21/0.66    inference(avatar_component_clause,[],[f139])).
% 2.21/0.66  fof(f88,plain,(
% 2.21/0.66    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.21/0.66    inference(definition_unfolding,[],[f63,f58])).
% 2.21/0.66  fof(f63,plain,(
% 2.21/0.66    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.21/0.66    inference(cnf_transformation,[],[f23])).
% 2.21/0.66  fof(f23,plain,(
% 2.21/0.66    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.21/0.66    inference(ennf_transformation,[],[f5])).
% 2.21/0.66  fof(f5,axiom,(
% 2.21/0.66    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.21/0.66  fof(f145,plain,(
% 2.21/0.66    spl4_5),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f144])).
% 2.21/0.66  fof(f144,plain,(
% 2.21/0.66    $false | spl4_5),
% 2.21/0.66    inference(subsumption_resolution,[],[f57,f137])).
% 2.21/0.66  fof(f137,plain,(
% 2.21/0.66    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.21/0.66    inference(avatar_component_clause,[],[f135])).
% 2.21/0.66  fof(f143,plain,(
% 2.21/0.66    ~spl4_5 | spl4_6),
% 2.21/0.66    inference(avatar_split_clause,[],[f133,f139,f135])).
% 2.21/0.66  fof(f133,plain,(
% 2.21/0.66    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.66    inference(superposition,[],[f49,f73])).
% 2.21/0.66  fof(f122,plain,(
% 2.21/0.66    spl4_4),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f119])).
% 2.21/0.66  fof(f119,plain,(
% 2.21/0.66    $false | spl4_4),
% 2.21/0.66    inference(unit_resulting_resolution,[],[f72,f113])).
% 2.21/0.66  fof(f113,plain,(
% 2.21/0.66    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.21/0.66    inference(avatar_component_clause,[],[f111])).
% 2.21/0.66  fof(f111,plain,(
% 2.21/0.66    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.21/0.66  fof(f72,plain,(
% 2.21/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/0.66    inference(cnf_transformation,[],[f2])).
% 2.21/0.66  fof(f2,axiom,(
% 2.21/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.21/0.66  fof(f118,plain,(
% 2.21/0.66    spl4_2),
% 2.21/0.66    inference(avatar_contradiction_clause,[],[f115])).
% 2.21/0.66  fof(f115,plain,(
% 2.21/0.66    $false | spl4_2),
% 2.21/0.66    inference(unit_resulting_resolution,[],[f72,f104])).
% 2.21/0.66  fof(f104,plain,(
% 2.21/0.66    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.21/0.66    inference(avatar_component_clause,[],[f102])).
% 2.21/0.66  fof(f102,plain,(
% 2.21/0.66    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.21/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.21/0.66  fof(f114,plain,(
% 2.21/0.66    spl4_3 | ~spl4_4),
% 2.21/0.66    inference(avatar_split_clause,[],[f95,f111,f107])).
% 2.21/0.66  fof(f95,plain,(
% 2.21/0.66    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.21/0.66    inference(resolution,[],[f66,f57])).
% 2.21/0.66  fof(f66,plain,(
% 2.21/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.21/0.66    inference(cnf_transformation,[],[f26])).
% 2.21/0.66  fof(f26,plain,(
% 2.21/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.66    inference(ennf_transformation,[],[f1])).
% 2.21/0.66  fof(f1,axiom,(
% 2.21/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.21/0.66  fof(f105,plain,(
% 2.21/0.66    spl4_1 | ~spl4_2),
% 2.21/0.66    inference(avatar_split_clause,[],[f94,f102,f98])).
% 2.21/0.66  fof(f94,plain,(
% 2.21/0.66    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.21/0.66    inference(resolution,[],[f66,f48])).
% 2.21/0.66  % SZS output end Proof for theBenchmark
% 2.21/0.66  % (24503)------------------------------
% 2.21/0.66  % (24503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.66  % (24503)Termination reason: Refutation
% 2.21/0.66  
% 2.21/0.66  % (24503)Memory used [KB]: 7803
% 2.21/0.66  % (24503)Time elapsed: 0.236 s
% 2.21/0.66  % (24503)------------------------------
% 2.21/0.66  % (24503)------------------------------
% 2.21/0.66  % (24489)Success in time 0.305 s
%------------------------------------------------------------------------------
