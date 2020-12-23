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
% DateTime   : Thu Dec  3 13:02:52 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  339 (1612 expanded)
%              Number of leaves         :   48 ( 521 expanded)
%              Depth                    :   28
%              Number of atoms          : 1382 (14396 expanded)
%              Number of equality atoms :  287 (4744 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1711,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f211,f251,f352,f358,f428,f431,f506,f529,f560,f786,f927,f1037,f1117,f1347,f1357,f1455,f1643,f1646,f1705])).

fof(f1705,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_34 ),
    inference(avatar_contradiction_clause,[],[f1704])).

fof(f1704,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1679,f262])).

fof(f262,plain,
    ( sK3 != k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f93,f210])).

fof(f210,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl4_2
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f93,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f76,f75])).

fof(f75,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f35,negated_conjecture,(
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
    inference(negated_conjecture,[],[f34])).

fof(f34,conjecture,(
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

fof(f1679,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_34 ),
    inference(backward_demodulation,[],[f566,f1678])).

fof(f1678,plain,
    ( sK2 = k4_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21
    | ~ spl4_34 ),
    inference(subsumption_resolution,[],[f1629,f1638])).

fof(f1638,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f1636])).

fof(f1636,plain,
    ( spl4_34
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f1629,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k4_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f1628,f276])).

fof(f276,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f254,f275])).

fof(f275,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f165,f88])).

fof(f88,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f165,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f84,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

fof(f254,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f205,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f205,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1628,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != k1_relat_1(sK3)
    | sK2 = k4_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f1627,f564])).

fof(f564,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_14 ),
    inference(resolution,[],[f550,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f550,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f1627,plain,
    ( sK2 = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f1626,f926])).

fof(f926,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f924])).

fof(f924,plain,
    ( spl4_21
  <=> sK2 = k2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1626,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(trivial_inequality_removal,[],[f1625])).

fof(f1625,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f1624,f442])).

fof(f442,plain,
    ( sK0 = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f255,f423])).

fof(f423,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl4_9
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f255,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f205,f129])).

fof(f1624,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1623,f346])).

fof(f346,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f345])).

fof(f345,plain,
    ( spl4_5
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1623,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1622,f268])).

fof(f268,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f267,f205])).

fof(f267,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f264,f82])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f264,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f104,f210])).

fof(f104,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1622,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1621,f774])).

fof(f774,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl4_18
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1621,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1620,f1549])).

fof(f1549,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1548,f550])).

fof(f1548,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1545,f85])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f77])).

fof(f1545,plain,
    ( v1_funct_1(k4_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(superposition,[],[f104,f1534])).

fof(f1534,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f1533,f550])).

fof(f1533,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f1528,f85])).

fof(f1528,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f301,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f301,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl4_3
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1620,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f1613,f921])).

fof(f921,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl4_20
  <=> v2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1613,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK3))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(superposition,[],[f142,f1459])).

fof(f1459,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1440,f149])).

fof(f149,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f127,f114,f114])).

fof(f114,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f127,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f1440,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(backward_demodulation,[],[f723,f1424])).

fof(f1424,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f411,f505])).

fof(f505,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl4_13
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f411,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f405,f85])).

fof(f405,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f168,f87])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f77])).

fof(f168,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f166,f82])).

fof(f166,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X1)
      | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f84,f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f723,plain,
    ( k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(resolution,[],[f252,f550])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k4_relat_1(k5_relat_1(sK2,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK2)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f205,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f142,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f99,f114])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f566,plain,
    ( sK3 = k4_relat_1(k4_relat_1(sK3))
    | ~ spl4_14 ),
    inference(resolution,[],[f550,f131])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f1646,plain,
    ( ~ spl4_14
    | spl4_35 ),
    inference(avatar_contradiction_clause,[],[f1645])).

fof(f1645,plain,
    ( $false
    | ~ spl4_14
    | spl4_35 ),
    inference(subsumption_resolution,[],[f1644,f578])).

fof(f578,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl4_14 ),
    inference(superposition,[],[f354,f571])).

fof(f571,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK0)
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f565,f279])).

fof(f279,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f171,f219])).

fof(f219,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f218,f85])).

fof(f218,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f217,f86])).

fof(f86,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f217,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f216,f87])).

fof(f216,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f215,f82])).

fof(f215,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f214,f83])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f77])).

fof(f214,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f213,f84])).

fof(f213,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f89,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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

fof(f89,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f77])).

fof(f171,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f87,f118])).

fof(f565,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl4_14 ),
    inference(resolution,[],[f550,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f354,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f353,f87])).

fof(f353,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    inference(superposition,[],[f140,f170])).

fof(f170,plain,(
    ! [X0] : k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0) ),
    inference(resolution,[],[f87,f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f1644,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1))
    | spl4_35 ),
    inference(resolution,[],[f1642,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1642,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_35 ),
    inference(avatar_component_clause,[],[f1640])).

fof(f1640,plain,
    ( spl4_35
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f1643,plain,
    ( spl4_34
    | ~ spl4_35
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f1598,f773,f549,f300,f1640,f1636])).

fof(f1598,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | sK1 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(resolution,[],[f1590,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1590,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f1589,f147])).

fof(f147,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f126,f114])).

fof(f126,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1589,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k1_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f1588,f564])).

fof(f1588,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3)))
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1587,f550])).

fof(f1587,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f1585,f774])).

fof(f1585,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3)))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(superposition,[],[f122,f1584])).

fof(f1584,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f1583,f1534])).

fof(f1583,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f243,f301])).

fof(f243,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f242,f85])).

fof(f242,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f241,f86])).

fof(f241,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f240,f87])).

fof(f240,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f227,f91])).

fof(f91,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f77])).

fof(f227,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f224])).

fof(f224,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f94,f219])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
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

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1455,plain,
    ( spl4_3
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f1454])).

fof(f1454,plain,
    ( $false
    | spl4_3
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f1429,f143])).

fof(f143,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f110,f114])).

fof(f110,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1429,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_3
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f608,f1424])).

fof(f608,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_3 ),
    inference(backward_demodulation,[],[f491,f411])).

fof(f491,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f490,f85])).

fof(f490,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f489,f91])).

fof(f489,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f488,f87])).

fof(f488,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_3 ),
    inference(subsumption_resolution,[],[f486,f302])).

fof(f302,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f300])).

fof(f486,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f188,f86])).

fof(f188,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f187,f82])).

fof(f187,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f186,f83])).

fof(f186,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f184,f84])).

fof(f184,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f177])).

fof(f177,plain,(
    ! [X2,X3] :
      ( sK1 != sK1
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f107,f88])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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

fof(f1357,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f1356])).

fof(f1356,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1355,f82])).

fof(f1355,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1354,f84])).

fof(f1354,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1353,f268])).

fof(f1353,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1352,f1031])).

fof(f1031,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1030,plain,
    ( spl4_28
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f1352,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_12
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1345,f501])).

fof(f501,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl4_12
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1345,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(superposition,[],[f116,f1130])).

fof(f1130,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f1129,f281])).

fof(f281,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f197,f210])).

fof(f197,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f196,f82])).

fof(f196,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f195,f83])).

fof(f195,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f194,f84])).

fof(f194,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f193,f90])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

fof(f193,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f182,f92])).

fof(f92,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

fof(f182,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f179])).

fof(f179,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f94,f88])).

fof(f1129,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f1122,f268])).

fof(f1122,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))
    | ~ spl4_28 ),
    inference(resolution,[],[f1031,f168])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1347,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_28
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f1346])).

fof(f1346,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_28
    | spl4_29 ),
    inference(subsumption_resolution,[],[f1342,f143])).

fof(f1342,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_28
    | spl4_29 ),
    inference(backward_demodulation,[],[f1036,f1130])).

fof(f1036,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)))
    | spl4_29 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1034,plain,
    ( spl4_29
  <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f1117,plain,
    ( ~ spl4_2
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f1116])).

fof(f1116,plain,
    ( $false
    | ~ spl4_2
    | spl4_28 ),
    inference(subsumption_resolution,[],[f1115,f1032])).

fof(f1032,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_28 ),
    inference(avatar_component_clause,[],[f1030])).

fof(f1115,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1114,f84])).

fof(f1114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f1113,f88])).

fof(f1113,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f272,f83])).

fof(f272,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK2,X3,X2)
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f271,f82])).

fof(f271,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK2,X3,X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f266,f90])).

fof(f266,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X3,X2,sK2) != X2
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ v1_funct_2(sK2,X3,X2)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_2 ),
    inference(superposition,[],[f98,f210])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
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

fof(f1037,plain,
    ( ~ spl4_28
    | ~ spl4_29
    | ~ spl4_1
    | ~ spl4_2
    | spl4_20 ),
    inference(avatar_split_clause,[],[f1011,f920,f208,f204,f1034,f1030])).

fof(f1011,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | spl4_20 ),
    inference(subsumption_resolution,[],[f493,f922])).

fof(f922,plain,
    ( ~ v2_funct_1(k4_relat_1(sK2))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f920])).

fof(f493,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f492,f268])).

fof(f492,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f487,f91])).

fof(f487,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f188,f261])).

fof(f261,plain,
    ( v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f192,f210])).

fof(f192,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f191,f82])).

fof(f191,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f83])).

fof(f190,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f189,f84])).

fof(f189,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f183,f90])).

fof(f183,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f178])).

fof(f178,plain,
    ( sK1 != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f97,f88])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f927,plain,
    ( ~ spl4_20
    | spl4_21
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f918,f421,f345,f208,f204,f924,f920])).

fof(f918,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f917])).

fof(f917,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f916,f423])).

fof(f916,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f293,f346])).

fof(f293,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f292,f275])).

fof(f292,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f291,f276])).

fof(f291,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f290,f255])).

fof(f290,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f289,f268])).

fof(f289,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f288,f205])).

fof(f288,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f284,f82])).

fof(f284,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2)))
    | sK2 = k2_funct_1(k4_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_2 ),
    inference(superposition,[],[f142,f281])).

fof(f786,plain,
    ( ~ spl4_14
    | spl4_18 ),
    inference(avatar_contradiction_clause,[],[f785])).

fof(f785,plain,
    ( $false
    | ~ spl4_14
    | spl4_18 ),
    inference(subsumption_resolution,[],[f783,f550])).

fof(f783,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_18 ),
    inference(resolution,[],[f775,f132])).

fof(f132,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f775,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f773])).

fof(f560,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f559])).

fof(f559,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f558,f120])).

fof(f120,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f558,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_14 ),
    inference(resolution,[],[f556,f87])).

fof(f556,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_14 ),
    inference(resolution,[],[f551,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f551,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f549])).

fof(f529,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f527,f82])).

fof(f527,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f526,f84])).

fof(f526,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f525,f85])).

fof(f525,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f523,f87])).

fof(f523,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_11 ),
    inference(resolution,[],[f497,f116])).

fof(f497,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f495])).

fof(f495,plain,
    ( spl4_11
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f506,plain,
    ( ~ spl4_11
    | ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f212,f503,f499,f495])).

fof(f212,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f89,f111])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f431,plain,
    ( ~ spl4_1
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | ~ spl4_1
    | spl4_10 ),
    inference(subsumption_resolution,[],[f429,f343])).

fof(f343,plain,
    ( m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(superposition,[],[f342,f308])).

fof(f308,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f256,f275])).

fof(f256,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f205,f130])).

fof(f342,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f341,f84])).

fof(f341,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f140,f164])).

fof(f164,plain,(
    ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0) ),
    inference(resolution,[],[f84,f138])).

fof(f429,plain,
    ( ~ m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))
    | spl4_10 ),
    inference(resolution,[],[f427,f133])).

fof(f427,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl4_10
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f428,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f379,f349,f425,f421])).

fof(f349,plain,
    ( spl4_6
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f379,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | sK0 = k1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f351,f137])).

fof(f351,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f349])).

fof(f358,plain,
    ( ~ spl4_1
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | ~ spl4_1
    | spl4_5 ),
    inference(subsumption_resolution,[],[f355,f205])).

fof(f355,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_5 ),
    inference(resolution,[],[f347,f132])).

fof(f347,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f345])).

fof(f352,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f287,f208,f204,f349,f345])).

fof(f287,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f286,f147])).

fof(f286,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f285,f255])).

fof(f285,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f283,f205])).

fof(f283,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f122,f281])).

fof(f251,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f248,f120])).

fof(f248,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f220,f84])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f206,f119])).

fof(f206,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f204])).

fof(f211,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f161,f208,f204])).

fof(f161,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f157,f82])).

fof(f157,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f90,f102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13051)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (13052)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (13047)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (13062)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (13046)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (13070)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (13058)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (13056)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (13057)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (13066)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (13068)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (13054)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (13059)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (13069)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (13061)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (13062)Refutation not found, incomplete strategy% (13062)------------------------------
% 0.20/0.53  % (13062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13075)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (13062)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13062)Memory used [KB]: 10746
% 0.20/0.53  % (13062)Time elapsed: 0.126 s
% 0.20/0.53  % (13062)------------------------------
% 0.20/0.53  % (13062)------------------------------
% 0.20/0.53  % (13048)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (13053)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (13050)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (13055)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (13071)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (13073)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (13049)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.55  % (13074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (13063)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (13065)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (13067)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.56  % (13064)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.56  % (13060)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.57  % (13072)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.74/0.59  % (13070)Refutation found. Thanks to Tanya!
% 1.74/0.59  % SZS status Theorem for theBenchmark
% 1.74/0.59  % SZS output start Proof for theBenchmark
% 1.74/0.59  fof(f1711,plain,(
% 1.74/0.59    $false),
% 1.74/0.59    inference(avatar_sat_refutation,[],[f211,f251,f352,f358,f428,f431,f506,f529,f560,f786,f927,f1037,f1117,f1347,f1357,f1455,f1643,f1646,f1705])).
% 1.74/0.59  fof(f1705,plain,(
% 1.74/0.59    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21 | ~spl4_34),
% 1.74/0.59    inference(avatar_contradiction_clause,[],[f1704])).
% 1.74/0.59  fof(f1704,plain,(
% 1.74/0.59    $false | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21 | ~spl4_34)),
% 1.74/0.59    inference(subsumption_resolution,[],[f1679,f262])).
% 1.74/0.59  fof(f262,plain,(
% 1.74/0.59    sK3 != k4_relat_1(sK2) | ~spl4_2),
% 1.74/0.59    inference(superposition,[],[f93,f210])).
% 1.74/0.59  fof(f210,plain,(
% 1.74/0.59    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl4_2),
% 1.74/0.59    inference(avatar_component_clause,[],[f208])).
% 1.74/0.59  fof(f208,plain,(
% 1.74/0.59    spl4_2 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.74/0.59  fof(f93,plain,(
% 1.74/0.59    k2_funct_1(sK2) != sK3),
% 1.74/0.59    inference(cnf_transformation,[],[f77])).
% 1.74/0.59  fof(f77,plain,(
% 1.74/0.59    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.74/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f76,f75])).
% 1.74/0.59  fof(f75,plain,(
% 1.74/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.74/0.59    introduced(choice_axiom,[])).
% 1.74/0.59  fof(f76,plain,(
% 1.74/0.59    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.74/0.59    introduced(choice_axiom,[])).
% 1.74/0.59  fof(f37,plain,(
% 1.74/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.74/0.59    inference(flattening,[],[f36])).
% 1.74/0.59  fof(f36,plain,(
% 1.74/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.74/0.59    inference(ennf_transformation,[],[f35])).
% 1.74/0.59  fof(f35,negated_conjecture,(
% 1.74/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.74/0.59    inference(negated_conjecture,[],[f34])).
% 1.74/0.59  fof(f34,conjecture,(
% 1.74/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.74/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.74/0.59  fof(f1679,plain,(
% 1.74/0.59    sK3 = k4_relat_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21 | ~spl4_34)),
% 1.74/0.59    inference(backward_demodulation,[],[f566,f1678])).
% 1.74/0.59  fof(f1678,plain,(
% 1.74/0.59    sK2 = k4_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21 | ~spl4_34)),
% 1.74/0.59    inference(subsumption_resolution,[],[f1629,f1638])).
% 1.74/0.59  fof(f1638,plain,(
% 1.74/0.59    sK1 = k1_relat_1(sK3) | ~spl4_34),
% 1.74/0.59    inference(avatar_component_clause,[],[f1636])).
% 1.74/0.59  fof(f1636,plain,(
% 1.74/0.59    spl4_34 <=> sK1 = k1_relat_1(sK3)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.74/0.59  fof(f1629,plain,(
% 1.74/0.59    sK1 != k1_relat_1(sK3) | sK2 = k4_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21)),
% 1.74/0.59    inference(forward_demodulation,[],[f1628,f276])).
% 1.74/0.59  fof(f276,plain,(
% 1.74/0.59    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 1.74/0.59    inference(backward_demodulation,[],[f254,f275])).
% 1.74/0.59  fof(f275,plain,(
% 1.74/0.59    sK1 = k2_relat_1(sK2)),
% 1.74/0.59    inference(forward_demodulation,[],[f165,f88])).
% 1.74/0.59  fof(f88,plain,(
% 1.74/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.74/0.59    inference(cnf_transformation,[],[f77])).
% 1.74/0.59  fof(f165,plain,(
% 1.74/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.74/0.59    inference(resolution,[],[f84,f118])).
% 1.74/0.59  fof(f118,plain,(
% 1.74/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.74/0.59    inference(cnf_transformation,[],[f60])).
% 1.74/0.59  fof(f60,plain,(
% 1.74/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.59    inference(ennf_transformation,[],[f23])).
% 1.74/0.59  fof(f23,axiom,(
% 1.74/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.74/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.74/0.59  fof(f84,plain,(
% 1.74/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.74/0.59    inference(cnf_transformation,[],[f77])).
% 1.74/0.59  fof(f254,plain,(
% 1.74/0.59    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 1.74/0.59    inference(resolution,[],[f205,f128])).
% 1.74/0.59  fof(f128,plain,(
% 1.74/0.59    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.74/0.59    inference(cnf_transformation,[],[f66])).
% 1.74/0.59  fof(f66,plain,(
% 1.74/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.59    inference(ennf_transformation,[],[f9])).
% 1.74/0.59  fof(f9,axiom,(
% 1.74/0.59    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.74/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.74/0.59  fof(f205,plain,(
% 1.74/0.59    v1_relat_1(sK2) | ~spl4_1),
% 1.74/0.59    inference(avatar_component_clause,[],[f204])).
% 1.74/0.59  fof(f204,plain,(
% 1.74/0.59    spl4_1 <=> v1_relat_1(sK2)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.74/0.59  fof(f1628,plain,(
% 1.74/0.59    k1_relat_1(k4_relat_1(sK2)) != k1_relat_1(sK3) | sK2 = k4_relat_1(sK3) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21)),
% 1.74/0.59    inference(forward_demodulation,[],[f1627,f564])).
% 1.74/0.59  fof(f564,plain,(
% 1.74/0.59    k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3)) | ~spl4_14),
% 1.74/0.59    inference(resolution,[],[f550,f129])).
% 1.74/0.59  fof(f129,plain,(
% 1.74/0.59    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 1.74/0.59    inference(cnf_transformation,[],[f66])).
% 1.74/0.59  fof(f550,plain,(
% 1.74/0.59    v1_relat_1(sK3) | ~spl4_14),
% 1.74/0.59    inference(avatar_component_clause,[],[f549])).
% 1.74/0.59  fof(f549,plain,(
% 1.74/0.59    spl4_14 <=> v1_relat_1(sK3)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.74/0.59  fof(f1627,plain,(
% 1.74/0.59    sK2 = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20 | ~spl4_21)),
% 1.74/0.59    inference(forward_demodulation,[],[f1626,f926])).
% 1.74/0.59  fof(f926,plain,(
% 1.74/0.59    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~spl4_21),
% 1.74/0.59    inference(avatar_component_clause,[],[f924])).
% 1.74/0.59  fof(f924,plain,(
% 1.74/0.59    spl4_21 <=> sK2 = k2_funct_1(k4_relat_1(sK2))),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.74/0.59  fof(f1626,plain,(
% 1.74/0.59    k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20)),
% 1.74/0.59    inference(trivial_inequality_removal,[],[f1625])).
% 1.74/0.59  fof(f1625,plain,(
% 1.74/0.59    k6_partfun1(sK0) != k6_partfun1(sK0) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_9 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20)),
% 1.74/0.59    inference(forward_demodulation,[],[f1624,f442])).
% 1.74/0.59  fof(f442,plain,(
% 1.74/0.59    sK0 = k2_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_9)),
% 1.74/0.59    inference(backward_demodulation,[],[f255,f423])).
% 1.74/0.59  fof(f423,plain,(
% 1.74/0.59    sK0 = k1_relat_1(sK2) | ~spl4_9),
% 1.74/0.59    inference(avatar_component_clause,[],[f421])).
% 1.74/0.59  fof(f421,plain,(
% 1.74/0.59    spl4_9 <=> sK0 = k1_relat_1(sK2)),
% 1.74/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.74/0.60  fof(f255,plain,(
% 1.74/0.60    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl4_1),
% 1.74/0.60    inference(resolution,[],[f205,f129])).
% 1.74/0.60  fof(f1624,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1623,f346])).
% 1.74/0.60  fof(f346,plain,(
% 1.74/0.60    v1_relat_1(k4_relat_1(sK2)) | ~spl4_5),
% 1.74/0.60    inference(avatar_component_clause,[],[f345])).
% 1.74/0.60  fof(f345,plain,(
% 1.74/0.60    spl4_5 <=> v1_relat_1(k4_relat_1(sK2))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.74/0.60  fof(f1623,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1622,f268])).
% 1.74/0.60  fof(f268,plain,(
% 1.74/0.60    v1_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f267,f205])).
% 1.74/0.60  fof(f267,plain,(
% 1.74/0.60    v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f264,f82])).
% 1.74/0.60  fof(f82,plain,(
% 1.74/0.60    v1_funct_1(sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f264,plain,(
% 1.74/0.60    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_2),
% 1.74/0.60    inference(superposition,[],[f104,f210])).
% 1.74/0.60  fof(f104,plain,(
% 1.74/0.60    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f49])).
% 1.74/0.60  fof(f49,plain,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f48])).
% 1.74/0.60  fof(f48,plain,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f17])).
% 1.74/0.60  fof(f17,axiom,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.74/0.60  fof(f1622,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_20)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1621,f774])).
% 1.74/0.60  fof(f774,plain,(
% 1.74/0.60    v1_relat_1(k4_relat_1(sK3)) | ~spl4_18),
% 1.74/0.60    inference(avatar_component_clause,[],[f773])).
% 1.74/0.60  fof(f773,plain,(
% 1.74/0.60    spl4_18 <=> v1_relat_1(k4_relat_1(sK3))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.74/0.60  fof(f1621,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_20)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1620,f1549])).
% 1.74/0.60  fof(f1549,plain,(
% 1.74/0.60    v1_funct_1(k4_relat_1(sK3)) | (~spl4_3 | ~spl4_14)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1548,f550])).
% 1.74/0.60  fof(f1548,plain,(
% 1.74/0.60    v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_14)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1545,f85])).
% 1.74/0.60  fof(f85,plain,(
% 1.74/0.60    v1_funct_1(sK3)),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f1545,plain,(
% 1.74/0.60    v1_funct_1(k4_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_14)),
% 1.74/0.60    inference(superposition,[],[f104,f1534])).
% 1.74/0.60  fof(f1534,plain,(
% 1.74/0.60    k2_funct_1(sK3) = k4_relat_1(sK3) | (~spl4_3 | ~spl4_14)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1533,f550])).
% 1.74/0.60  fof(f1533,plain,(
% 1.74/0.60    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_relat_1(sK3) | ~spl4_3),
% 1.74/0.60    inference(subsumption_resolution,[],[f1528,f85])).
% 1.74/0.60  fof(f1528,plain,(
% 1.74/0.60    k2_funct_1(sK3) = k4_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_3),
% 1.74/0.60    inference(resolution,[],[f301,f102])).
% 1.74/0.60  fof(f102,plain,(
% 1.74/0.60    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f47])).
% 1.74/0.60  fof(f47,plain,(
% 1.74/0.60    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f46])).
% 1.74/0.60  fof(f46,plain,(
% 1.74/0.60    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f16])).
% 1.74/0.60  fof(f16,axiom,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.74/0.60  fof(f301,plain,(
% 1.74/0.60    v2_funct_1(sK3) | ~spl4_3),
% 1.74/0.60    inference(avatar_component_clause,[],[f300])).
% 1.74/0.60  fof(f300,plain,(
% 1.74/0.60    spl4_3 <=> v2_funct_1(sK3)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.74/0.60  fof(f1620,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_13 | ~spl4_14 | ~spl4_20)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1613,f921])).
% 1.74/0.60  fof(f921,plain,(
% 1.74/0.60    v2_funct_1(k4_relat_1(sK2)) | ~spl4_20),
% 1.74/0.60    inference(avatar_component_clause,[],[f920])).
% 1.74/0.60  fof(f920,plain,(
% 1.74/0.60    spl4_20 <=> v2_funct_1(k4_relat_1(sK2))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.74/0.60  fof(f1613,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK3)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_13 | ~spl4_14)),
% 1.74/0.60    inference(superposition,[],[f142,f1459])).
% 1.74/0.60  fof(f1459,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_13 | ~spl4_14)),
% 1.74/0.60    inference(forward_demodulation,[],[f1440,f149])).
% 1.74/0.60  fof(f149,plain,(
% 1.74/0.60    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f127,f114,f114])).
% 1.74/0.60  fof(f114,plain,(
% 1.74/0.60    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f29])).
% 1.74/0.60  fof(f29,axiom,(
% 1.74/0.60    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.74/0.60  fof(f127,plain,(
% 1.74/0.60    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f13])).
% 1.74/0.60  fof(f13,axiom,(
% 1.74/0.60    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 1.74/0.60  fof(f1440,plain,(
% 1.74/0.60    k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) | (~spl4_1 | ~spl4_13 | ~spl4_14)),
% 1.74/0.60    inference(backward_demodulation,[],[f723,f1424])).
% 1.74/0.60  fof(f1424,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_13),
% 1.74/0.60    inference(backward_demodulation,[],[f411,f505])).
% 1.74/0.60  fof(f505,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl4_13),
% 1.74/0.60    inference(avatar_component_clause,[],[f503])).
% 1.74/0.60  fof(f503,plain,(
% 1.74/0.60    spl4_13 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.74/0.60  fof(f411,plain,(
% 1.74/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f405,f85])).
% 1.74/0.60  fof(f405,plain,(
% 1.74/0.60    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.74/0.60    inference(resolution,[],[f168,f87])).
% 1.74/0.60  fof(f87,plain,(
% 1.74/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f168,plain,(
% 1.74/0.60    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f166,f82])).
% 1.74/0.60  fof(f166,plain,(
% 1.74/0.60    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X1) | k1_partfun1(sK0,sK1,X2,X3,sK2,X1) = k5_relat_1(sK2,X1) | ~v1_funct_1(sK2)) )),
% 1.74/0.60    inference(resolution,[],[f84,f117])).
% 1.74/0.60  fof(f117,plain,(
% 1.74/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f59])).
% 1.74/0.60  fof(f59,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.74/0.60    inference(flattening,[],[f58])).
% 1.74/0.60  fof(f58,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.74/0.60    inference(ennf_transformation,[],[f28])).
% 1.74/0.60  fof(f28,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.74/0.60  fof(f723,plain,(
% 1.74/0.60    k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) | (~spl4_1 | ~spl4_14)),
% 1.74/0.60    inference(resolution,[],[f252,f550])).
% 1.74/0.60  fof(f252,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k5_relat_1(sK2,X0)) = k5_relat_1(k4_relat_1(X0),k4_relat_1(sK2))) ) | ~spl4_1),
% 1.74/0.60    inference(resolution,[],[f205,f121])).
% 1.74/0.60  fof(f121,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f62])).
% 1.74/0.60  fof(f62,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f11])).
% 1.74/0.60  fof(f11,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 1.74/0.60  fof(f142,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(definition_unfolding,[],[f99,f114])).
% 1.74/0.60  fof(f99,plain,(
% 1.74/0.60    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f43])).
% 1.74/0.60  fof(f43,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(flattening,[],[f42])).
% 1.74/0.60  fof(f42,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.74/0.60    inference(ennf_transformation,[],[f21])).
% 1.74/0.60  fof(f21,axiom,(
% 1.74/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.74/0.60  fof(f566,plain,(
% 1.74/0.60    sK3 = k4_relat_1(k4_relat_1(sK3)) | ~spl4_14),
% 1.74/0.60    inference(resolution,[],[f550,f131])).
% 1.74/0.60  fof(f131,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f68])).
% 1.74/0.60  fof(f68,plain,(
% 1.74/0.60    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f6])).
% 1.74/0.60  fof(f6,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 1.74/0.60  fof(f1646,plain,(
% 1.74/0.60    ~spl4_14 | spl4_35),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1645])).
% 1.74/0.60  fof(f1645,plain,(
% 1.74/0.60    $false | (~spl4_14 | spl4_35)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1644,f578])).
% 1.74/0.60  fof(f578,plain,(
% 1.74/0.60    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl4_14),
% 1.74/0.60    inference(superposition,[],[f354,f571])).
% 1.74/0.60  fof(f571,plain,(
% 1.74/0.60    k1_relat_1(sK3) = k10_relat_1(sK3,sK0) | ~spl4_14),
% 1.74/0.60    inference(forward_demodulation,[],[f565,f279])).
% 1.74/0.60  fof(f279,plain,(
% 1.74/0.60    sK0 = k2_relat_1(sK3)),
% 1.74/0.60    inference(forward_demodulation,[],[f171,f219])).
% 1.74/0.60  fof(f219,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f218,f85])).
% 1.74/0.60  fof(f218,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f217,f86])).
% 1.74/0.60  fof(f86,plain,(
% 1.74/0.60    v1_funct_2(sK3,sK1,sK0)),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f217,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f216,f87])).
% 1.74/0.60  fof(f216,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f215,f82])).
% 1.74/0.60  fof(f215,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f214,f83])).
% 1.74/0.60  fof(f83,plain,(
% 1.74/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f214,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f213,f84])).
% 1.74/0.60  fof(f213,plain,(
% 1.74/0.60    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(resolution,[],[f89,f113])).
% 1.74/0.60  fof(f113,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f55])).
% 1.74/0.60  fof(f55,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.74/0.60    inference(flattening,[],[f54])).
% 1.74/0.60  fof(f54,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.74/0.60    inference(ennf_transformation,[],[f30])).
% 1.74/0.60  fof(f30,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.74/0.60  fof(f89,plain,(
% 1.74/0.60    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f171,plain,(
% 1.74/0.60    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.74/0.60    inference(resolution,[],[f87,f118])).
% 1.74/0.60  fof(f565,plain,(
% 1.74/0.60    k1_relat_1(sK3) = k10_relat_1(sK3,k2_relat_1(sK3)) | ~spl4_14),
% 1.74/0.60    inference(resolution,[],[f550,f130])).
% 1.74/0.60  fof(f130,plain,(
% 1.74/0.60    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f67])).
% 1.74/0.60  fof(f67,plain,(
% 1.74/0.60    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f8])).
% 1.74/0.60  fof(f8,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.74/0.60  fof(f354,plain,(
% 1.74/0.60    ( ! [X0] : (m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f353,f87])).
% 1.74/0.60  fof(f353,plain,(
% 1.74/0.60    ( ! [X0] : (m1_subset_1(k10_relat_1(sK3,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) )),
% 1.74/0.60    inference(superposition,[],[f140,f170])).
% 1.74/0.60  fof(f170,plain,(
% 1.74/0.60    ( ! [X0] : (k8_relset_1(sK1,sK0,sK3,X0) = k10_relat_1(sK3,X0)) )),
% 1.74/0.60    inference(resolution,[],[f87,f138])).
% 1.74/0.60  fof(f138,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f70])).
% 1.74/0.60  fof(f70,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f24])).
% 1.74/0.60  fof(f24,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.74/0.60  fof(f140,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f73])).
% 1.74/0.60  fof(f73,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(ennf_transformation,[],[f22])).
% 1.74/0.60  fof(f22,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 1.74/0.60  fof(f1644,plain,(
% 1.74/0.60    ~m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK1)) | spl4_35),
% 1.74/0.60    inference(resolution,[],[f1642,f133])).
% 1.74/0.60  fof(f133,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f79])).
% 1.74/0.60  fof(f79,plain,(
% 1.74/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.74/0.60    inference(nnf_transformation,[],[f2])).
% 1.74/0.60  fof(f2,axiom,(
% 1.74/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.74/0.60  fof(f1642,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_35),
% 1.74/0.60    inference(avatar_component_clause,[],[f1640])).
% 1.74/0.60  fof(f1640,plain,(
% 1.74/0.60    spl4_35 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.74/0.60  fof(f1643,plain,(
% 1.74/0.60    spl4_34 | ~spl4_35 | ~spl4_3 | ~spl4_14 | ~spl4_18),
% 1.74/0.60    inference(avatar_split_clause,[],[f1598,f773,f549,f300,f1640,f1636])).
% 1.74/0.60  fof(f1598,plain,(
% 1.74/0.60    ~r1_tarski(k1_relat_1(sK3),sK1) | sK1 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_14 | ~spl4_18)),
% 1.74/0.60    inference(resolution,[],[f1590,f137])).
% 1.74/0.60  fof(f137,plain,(
% 1.74/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.74/0.60    inference(cnf_transformation,[],[f81])).
% 1.74/0.60  fof(f81,plain,(
% 1.74/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.74/0.60    inference(flattening,[],[f80])).
% 1.74/0.60  fof(f80,plain,(
% 1.74/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.74/0.60    inference(nnf_transformation,[],[f1])).
% 1.74/0.60  fof(f1,axiom,(
% 1.74/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.74/0.60  fof(f1590,plain,(
% 1.74/0.60    r1_tarski(sK1,k1_relat_1(sK3)) | (~spl4_3 | ~spl4_14 | ~spl4_18)),
% 1.74/0.60    inference(forward_demodulation,[],[f1589,f147])).
% 1.74/0.60  fof(f147,plain,(
% 1.74/0.60    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.74/0.60    inference(definition_unfolding,[],[f126,f114])).
% 1.74/0.60  fof(f126,plain,(
% 1.74/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.74/0.60    inference(cnf_transformation,[],[f12])).
% 1.74/0.60  fof(f12,axiom,(
% 1.74/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.74/0.60  fof(f1589,plain,(
% 1.74/0.60    r1_tarski(k2_relat_1(k6_partfun1(sK1)),k1_relat_1(sK3)) | (~spl4_3 | ~spl4_14 | ~spl4_18)),
% 1.74/0.60    inference(forward_demodulation,[],[f1588,f564])).
% 1.74/0.60  fof(f1588,plain,(
% 1.74/0.60    r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3))) | (~spl4_3 | ~spl4_14 | ~spl4_18)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1587,f550])).
% 1.74/0.60  fof(f1587,plain,(
% 1.74/0.60    r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3))) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_14 | ~spl4_18)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1585,f774])).
% 1.74/0.60  fof(f1585,plain,(
% 1.74/0.60    r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k4_relat_1(sK3))) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_14)),
% 1.74/0.60    inference(superposition,[],[f122,f1584])).
% 1.74/0.60  fof(f1584,plain,(
% 1.74/0.60    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) | (~spl4_3 | ~spl4_14)),
% 1.74/0.60    inference(forward_demodulation,[],[f1583,f1534])).
% 1.74/0.60  fof(f1583,plain,(
% 1.74/0.60    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_3),
% 1.74/0.60    inference(subsumption_resolution,[],[f243,f301])).
% 1.74/0.60  fof(f243,plain,(
% 1.74/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.74/0.60    inference(subsumption_resolution,[],[f242,f85])).
% 1.74/0.60  fof(f242,plain,(
% 1.74/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f241,f86])).
% 1.74/0.60  fof(f241,plain,(
% 1.74/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f240,f87])).
% 1.74/0.60  fof(f240,plain,(
% 1.74/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(subsumption_resolution,[],[f227,f91])).
% 1.74/0.60  fof(f91,plain,(
% 1.74/0.60    k1_xboole_0 != sK0),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f227,plain,(
% 1.74/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f224])).
% 1.74/0.60  fof(f224,plain,(
% 1.74/0.60    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(superposition,[],[f94,f219])).
% 1.74/0.60  fof(f94,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f39])).
% 1.74/0.60  fof(f39,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.74/0.60    inference(flattening,[],[f38])).
% 1.74/0.60  fof(f38,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.74/0.60    inference(ennf_transformation,[],[f33])).
% 1.74/0.60  fof(f33,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.74/0.60  fof(f122,plain,(
% 1.74/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f63])).
% 1.74/0.60  fof(f63,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f10])).
% 1.74/0.60  fof(f10,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.74/0.60  fof(f1455,plain,(
% 1.74/0.60    spl4_3 | ~spl4_13),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1454])).
% 1.74/0.60  fof(f1454,plain,(
% 1.74/0.60    $false | (spl4_3 | ~spl4_13)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1429,f143])).
% 1.74/0.60  fof(f143,plain,(
% 1.74/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.74/0.60    inference(definition_unfolding,[],[f110,f114])).
% 1.74/0.60  fof(f110,plain,(
% 1.74/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f18])).
% 1.74/0.60  fof(f18,axiom,(
% 1.74/0.60    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.74/0.60  fof(f1429,plain,(
% 1.74/0.60    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_3 | ~spl4_13)),
% 1.74/0.60    inference(backward_demodulation,[],[f608,f1424])).
% 1.74/0.60  fof(f608,plain,(
% 1.74/0.60    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_3),
% 1.74/0.60    inference(backward_demodulation,[],[f491,f411])).
% 1.74/0.60  fof(f491,plain,(
% 1.74/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_3),
% 1.74/0.60    inference(subsumption_resolution,[],[f490,f85])).
% 1.74/0.60  fof(f490,plain,(
% 1.74/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl4_3),
% 1.74/0.60    inference(subsumption_resolution,[],[f489,f91])).
% 1.74/0.60  fof(f489,plain,(
% 1.74/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_3),
% 1.74/0.60    inference(subsumption_resolution,[],[f488,f87])).
% 1.74/0.60  fof(f488,plain,(
% 1.74/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_3),
% 1.74/0.60    inference(subsumption_resolution,[],[f486,f302])).
% 1.74/0.60  fof(f302,plain,(
% 1.74/0.60    ~v2_funct_1(sK3) | spl4_3),
% 1.74/0.60    inference(avatar_component_clause,[],[f300])).
% 1.74/0.60  fof(f486,plain,(
% 1.74/0.60    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.74/0.60    inference(resolution,[],[f188,f86])).
% 1.74/0.60  fof(f188,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f187,f82])).
% 1.74/0.60  fof(f187,plain,(
% 1.74/0.60    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f186,f83])).
% 1.74/0.60  fof(f186,plain,(
% 1.74/0.60    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.74/0.60    inference(subsumption_resolution,[],[f184,f84])).
% 1.74/0.60  fof(f184,plain,(
% 1.74/0.60    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f177])).
% 1.74/0.60  fof(f177,plain,(
% 1.74/0.60    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.74/0.60    inference(superposition,[],[f107,f88])).
% 1.74/0.60  fof(f107,plain,(
% 1.74/0.60    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f51])).
% 1.74/0.60  fof(f51,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.74/0.60    inference(flattening,[],[f50])).
% 1.74/0.60  fof(f50,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.74/0.60    inference(ennf_transformation,[],[f31])).
% 1.74/0.60  fof(f31,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.74/0.60  fof(f1357,plain,(
% 1.74/0.60    ~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_28),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1356])).
% 1.74/0.60  fof(f1356,plain,(
% 1.74/0.60    $false | (~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1355,f82])).
% 1.74/0.60  fof(f1355,plain,(
% 1.74/0.60    ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1354,f84])).
% 1.74/0.60  fof(f1354,plain,(
% 1.74/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1353,f268])).
% 1.74/0.60  fof(f1353,plain,(
% 1.74/0.60    ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1352,f1031])).
% 1.74/0.60  fof(f1031,plain,(
% 1.74/0.60    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_28),
% 1.74/0.60    inference(avatar_component_clause,[],[f1030])).
% 1.74/0.60  fof(f1030,plain,(
% 1.74/0.60    spl4_28 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.74/0.60  fof(f1352,plain,(
% 1.74/0.60    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | spl4_12 | ~spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1345,f501])).
% 1.74/0.60  fof(f501,plain,(
% 1.74/0.60    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_12),
% 1.74/0.60    inference(avatar_component_clause,[],[f499])).
% 1.74/0.60  fof(f499,plain,(
% 1.74/0.60    spl4_12 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.74/0.60  fof(f1345,plain,(
% 1.74/0.60    m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_1 | ~spl4_2 | ~spl4_28)),
% 1.74/0.60    inference(superposition,[],[f116,f1130])).
% 1.74/0.60  fof(f1130,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_28)),
% 1.74/0.60    inference(forward_demodulation,[],[f1129,f281])).
% 1.74/0.60  fof(f281,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) | ~spl4_2),
% 1.74/0.60    inference(forward_demodulation,[],[f197,f210])).
% 1.74/0.60  fof(f197,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.74/0.60    inference(subsumption_resolution,[],[f196,f82])).
% 1.74/0.60  fof(f196,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f195,f83])).
% 1.74/0.60  fof(f195,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f194,f84])).
% 1.74/0.60  fof(f194,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f193,f90])).
% 1.74/0.60  fof(f90,plain,(
% 1.74/0.60    v2_funct_1(sK2)),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f193,plain,(
% 1.74/0.60    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f182,f92])).
% 1.74/0.60  fof(f92,plain,(
% 1.74/0.60    k1_xboole_0 != sK1),
% 1.74/0.60    inference(cnf_transformation,[],[f77])).
% 1.74/0.60  fof(f182,plain,(
% 1.74/0.60    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f179])).
% 1.74/0.60  fof(f179,plain,(
% 1.74/0.60    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(superposition,[],[f94,f88])).
% 1.74/0.60  fof(f1129,plain,(
% 1.74/0.60    k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1122,f268])).
% 1.74/0.60  fof(f1122,plain,(
% 1.74/0.60    ~v1_funct_1(k4_relat_1(sK2)) | k5_relat_1(sK2,k4_relat_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) | ~spl4_28),
% 1.74/0.60    inference(resolution,[],[f1031,f168])).
% 1.74/0.60  fof(f116,plain,(
% 1.74/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f57])).
% 1.74/0.60  fof(f57,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.74/0.60    inference(flattening,[],[f56])).
% 1.74/0.60  fof(f56,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.74/0.60    inference(ennf_transformation,[],[f26])).
% 1.74/0.60  fof(f26,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.74/0.60  fof(f1347,plain,(
% 1.74/0.60    ~spl4_1 | ~spl4_2 | ~spl4_28 | spl4_29),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1346])).
% 1.74/0.60  fof(f1346,plain,(
% 1.74/0.60    $false | (~spl4_1 | ~spl4_2 | ~spl4_28 | spl4_29)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1342,f143])).
% 1.74/0.60  fof(f1342,plain,(
% 1.74/0.60    ~v2_funct_1(k6_partfun1(sK0)) | (~spl4_1 | ~spl4_2 | ~spl4_28 | spl4_29)),
% 1.74/0.60    inference(backward_demodulation,[],[f1036,f1130])).
% 1.74/0.60  fof(f1036,plain,(
% 1.74/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))) | spl4_29),
% 1.74/0.60    inference(avatar_component_clause,[],[f1034])).
% 1.74/0.60  fof(f1034,plain,(
% 1.74/0.60    spl4_29 <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 1.74/0.60  fof(f1117,plain,(
% 1.74/0.60    ~spl4_2 | spl4_28),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f1116])).
% 1.74/0.60  fof(f1116,plain,(
% 1.74/0.60    $false | (~spl4_2 | spl4_28)),
% 1.74/0.60    inference(subsumption_resolution,[],[f1115,f1032])).
% 1.74/0.60  fof(f1032,plain,(
% 1.74/0.60    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_28),
% 1.74/0.60    inference(avatar_component_clause,[],[f1030])).
% 1.74/0.60  fof(f1115,plain,(
% 1.74/0.60    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f1114,f84])).
% 1.74/0.60  fof(f1114,plain,(
% 1.74/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f1113,f88])).
% 1.74/0.60  fof(f1113,plain,(
% 1.74/0.60    sK1 != k2_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_2),
% 1.74/0.60    inference(resolution,[],[f272,f83])).
% 1.74/0.60  fof(f272,plain,(
% 1.74/0.60    ( ! [X2,X3] : (~v1_funct_2(sK2,X3,X2) | k2_relset_1(X3,X2,sK2) != X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f271,f82])).
% 1.74/0.60  fof(f271,plain,(
% 1.74/0.60    ( ! [X2,X3] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X3,X2,sK2) != X2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK2,X3,X2) | ~v1_funct_1(sK2)) ) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f266,f90])).
% 1.74/0.60  fof(f266,plain,(
% 1.74/0.60    ( ! [X2,X3] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X3,X2,sK2) != X2 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK2,X3,X2) | ~v1_funct_1(sK2)) ) | ~spl4_2),
% 1.74/0.60    inference(superposition,[],[f98,f210])).
% 1.74/0.60  fof(f98,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f41])).
% 1.74/0.60  fof(f41,plain,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.74/0.60    inference(flattening,[],[f40])).
% 1.74/0.60  fof(f40,plain,(
% 1.74/0.60    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.74/0.60    inference(ennf_transformation,[],[f32])).
% 1.74/0.60  fof(f32,axiom,(
% 1.74/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.74/0.60  fof(f1037,plain,(
% 1.74/0.60    ~spl4_28 | ~spl4_29 | ~spl4_1 | ~spl4_2 | spl4_20),
% 1.74/0.60    inference(avatar_split_clause,[],[f1011,f920,f208,f204,f1034,f1030])).
% 1.74/0.60  fof(f1011,plain,(
% 1.74/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_1 | ~spl4_2 | spl4_20)),
% 1.74/0.60    inference(subsumption_resolution,[],[f493,f922])).
% 1.74/0.60  fof(f922,plain,(
% 1.74/0.60    ~v2_funct_1(k4_relat_1(sK2)) | spl4_20),
% 1.74/0.60    inference(avatar_component_clause,[],[f920])).
% 1.74/0.60  fof(f493,plain,(
% 1.74/0.60    v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f492,f268])).
% 1.74/0.60  fof(f492,plain,(
% 1.74/0.60    v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f487,f91])).
% 1.74/0.60  fof(f487,plain,(
% 1.74/0.60    v2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.74/0.60    inference(resolution,[],[f188,f261])).
% 1.74/0.60  fof(f261,plain,(
% 1.74/0.60    v1_funct_2(k4_relat_1(sK2),sK1,sK0) | ~spl4_2),
% 1.74/0.60    inference(backward_demodulation,[],[f192,f210])).
% 1.74/0.60  fof(f192,plain,(
% 1.74/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.74/0.60    inference(subsumption_resolution,[],[f191,f82])).
% 1.74/0.60  fof(f191,plain,(
% 1.74/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f190,f83])).
% 1.74/0.60  fof(f190,plain,(
% 1.74/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f189,f84])).
% 1.74/0.60  fof(f189,plain,(
% 1.74/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f183,f90])).
% 1.74/0.60  fof(f183,plain,(
% 1.74/0.60    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f178])).
% 1.74/0.60  fof(f178,plain,(
% 1.74/0.60    sK1 != sK1 | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.74/0.60    inference(superposition,[],[f97,f88])).
% 1.74/0.60  fof(f97,plain,(
% 1.74/0.60    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f41])).
% 1.74/0.60  fof(f927,plain,(
% 1.74/0.60    ~spl4_20 | spl4_21 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_9),
% 1.74/0.60    inference(avatar_split_clause,[],[f918,f421,f345,f208,f204,f924,f920])).
% 1.74/0.60  fof(f918,plain,(
% 1.74/0.60    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_9)),
% 1.74/0.60    inference(trivial_inequality_removal,[],[f917])).
% 1.74/0.60  fof(f917,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_9)),
% 1.74/0.60    inference(forward_demodulation,[],[f916,f423])).
% 1.74/0.60  fof(f916,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 1.74/0.60    inference(subsumption_resolution,[],[f293,f346])).
% 1.74/0.60  fof(f293,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f292,f275])).
% 1.74/0.60  fof(f292,plain,(
% 1.74/0.60    sK1 != k2_relat_1(sK2) | k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(forward_demodulation,[],[f291,f276])).
% 1.74/0.60  fof(f291,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k4_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(forward_demodulation,[],[f290,f255])).
% 1.74/0.60  fof(f290,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f289,f268])).
% 1.74/0.60  fof(f289,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.60    inference(subsumption_resolution,[],[f288,f205])).
% 1.74/0.60  fof(f288,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.74/0.60    inference(subsumption_resolution,[],[f284,f82])).
% 1.74/0.60  fof(f284,plain,(
% 1.74/0.60    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(k4_relat_1(sK2))) | sK2 = k2_funct_1(k4_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_2),
% 1.74/0.60    inference(superposition,[],[f142,f281])).
% 1.74/0.60  fof(f786,plain,(
% 1.74/0.60    ~spl4_14 | spl4_18),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f785])).
% 1.74/0.60  fof(f785,plain,(
% 1.74/0.60    $false | (~spl4_14 | spl4_18)),
% 1.74/0.60    inference(subsumption_resolution,[],[f783,f550])).
% 1.74/0.60  fof(f783,plain,(
% 1.74/0.60    ~v1_relat_1(sK3) | spl4_18),
% 1.74/0.60    inference(resolution,[],[f775,f132])).
% 1.74/0.60  fof(f132,plain,(
% 1.74/0.60    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f69])).
% 1.74/0.60  fof(f69,plain,(
% 1.74/0.60    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f4])).
% 1.74/0.60  fof(f4,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 1.74/0.60  fof(f775,plain,(
% 1.74/0.60    ~v1_relat_1(k4_relat_1(sK3)) | spl4_18),
% 1.74/0.60    inference(avatar_component_clause,[],[f773])).
% 1.74/0.60  fof(f560,plain,(
% 1.74/0.60    spl4_14),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f559])).
% 1.74/0.60  fof(f559,plain,(
% 1.74/0.60    $false | spl4_14),
% 1.74/0.60    inference(subsumption_resolution,[],[f558,f120])).
% 1.74/0.60  fof(f120,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f5])).
% 1.74/0.60  fof(f5,axiom,(
% 1.74/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.74/0.60  fof(f558,plain,(
% 1.74/0.60    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_14),
% 1.74/0.60    inference(resolution,[],[f556,f87])).
% 1.74/0.60  fof(f556,plain,(
% 1.74/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_14),
% 1.74/0.60    inference(resolution,[],[f551,f119])).
% 1.74/0.60  fof(f119,plain,(
% 1.74/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.74/0.60    inference(cnf_transformation,[],[f61])).
% 1.74/0.60  fof(f61,plain,(
% 1.74/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.74/0.60    inference(ennf_transformation,[],[f3])).
% 1.74/0.60  fof(f3,axiom,(
% 1.74/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.74/0.60  fof(f551,plain,(
% 1.74/0.60    ~v1_relat_1(sK3) | spl4_14),
% 1.74/0.60    inference(avatar_component_clause,[],[f549])).
% 1.74/0.60  fof(f529,plain,(
% 1.74/0.60    spl4_11),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f528])).
% 1.74/0.60  fof(f528,plain,(
% 1.74/0.60    $false | spl4_11),
% 1.74/0.60    inference(subsumption_resolution,[],[f527,f82])).
% 1.74/0.60  fof(f527,plain,(
% 1.74/0.60    ~v1_funct_1(sK2) | spl4_11),
% 1.74/0.60    inference(subsumption_resolution,[],[f526,f84])).
% 1.74/0.60  fof(f526,plain,(
% 1.74/0.60    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_11),
% 1.74/0.60    inference(subsumption_resolution,[],[f525,f85])).
% 1.74/0.60  fof(f525,plain,(
% 1.74/0.60    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_11),
% 1.74/0.60    inference(subsumption_resolution,[],[f523,f87])).
% 1.74/0.60  fof(f523,plain,(
% 1.74/0.60    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_11),
% 1.74/0.60    inference(resolution,[],[f497,f116])).
% 1.74/0.60  fof(f497,plain,(
% 1.74/0.60    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_11),
% 1.74/0.60    inference(avatar_component_clause,[],[f495])).
% 1.74/0.60  fof(f495,plain,(
% 1.74/0.60    spl4_11 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.74/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.74/0.60  fof(f506,plain,(
% 1.74/0.60    ~spl4_11 | ~spl4_12 | spl4_13),
% 1.74/0.60    inference(avatar_split_clause,[],[f212,f503,f499,f495])).
% 1.74/0.60  fof(f212,plain,(
% 1.74/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.74/0.60    inference(resolution,[],[f89,f111])).
% 1.74/0.60  fof(f111,plain,(
% 1.74/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.74/0.60    inference(cnf_transformation,[],[f78])).
% 1.74/0.60  fof(f78,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(nnf_transformation,[],[f53])).
% 1.74/0.60  fof(f53,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.74/0.60    inference(flattening,[],[f52])).
% 1.74/0.60  fof(f52,plain,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.74/0.60    inference(ennf_transformation,[],[f25])).
% 1.74/0.60  fof(f25,axiom,(
% 1.74/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.74/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.74/0.60  fof(f431,plain,(
% 1.74/0.60    ~spl4_1 | spl4_10),
% 1.74/0.60    inference(avatar_contradiction_clause,[],[f430])).
% 1.74/0.60  fof(f430,plain,(
% 1.74/0.60    $false | (~spl4_1 | spl4_10)),
% 1.74/0.60    inference(subsumption_resolution,[],[f429,f343])).
% 1.74/0.61  fof(f343,plain,(
% 1.74/0.61    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_1),
% 1.74/0.61    inference(superposition,[],[f342,f308])).
% 1.74/0.61  fof(f308,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl4_1),
% 1.74/0.61    inference(forward_demodulation,[],[f256,f275])).
% 1.74/0.61  fof(f256,plain,(
% 1.74/0.61    k1_relat_1(sK2) = k10_relat_1(sK2,k2_relat_1(sK2)) | ~spl4_1),
% 1.74/0.61    inference(resolution,[],[f205,f130])).
% 1.74/0.61  fof(f342,plain,(
% 1.74/0.61    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0))) )),
% 1.74/0.61    inference(subsumption_resolution,[],[f341,f84])).
% 1.74/0.61  fof(f341,plain,(
% 1.74/0.61    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.74/0.61    inference(superposition,[],[f140,f164])).
% 1.74/0.61  fof(f164,plain,(
% 1.74/0.61    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(sK0,sK1,sK2,X0)) )),
% 1.74/0.61    inference(resolution,[],[f84,f138])).
% 1.74/0.61  fof(f429,plain,(
% 1.74/0.61    ~m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) | spl4_10),
% 1.74/0.61    inference(resolution,[],[f427,f133])).
% 1.74/0.61  fof(f427,plain,(
% 1.74/0.61    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_10),
% 1.74/0.61    inference(avatar_component_clause,[],[f425])).
% 1.74/0.61  fof(f425,plain,(
% 1.74/0.61    spl4_10 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.74/0.61  fof(f428,plain,(
% 1.74/0.61    spl4_9 | ~spl4_10 | ~spl4_6),
% 1.74/0.61    inference(avatar_split_clause,[],[f379,f349,f425,f421])).
% 1.74/0.61  fof(f349,plain,(
% 1.74/0.61    spl4_6 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 1.74/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.74/0.61  fof(f379,plain,(
% 1.74/0.61    ~r1_tarski(k1_relat_1(sK2),sK0) | sK0 = k1_relat_1(sK2) | ~spl4_6),
% 1.74/0.61    inference(resolution,[],[f351,f137])).
% 1.74/0.61  fof(f351,plain,(
% 1.74/0.61    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl4_6),
% 1.74/0.61    inference(avatar_component_clause,[],[f349])).
% 1.74/0.61  fof(f358,plain,(
% 1.74/0.61    ~spl4_1 | spl4_5),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f357])).
% 1.74/0.61  fof(f357,plain,(
% 1.74/0.61    $false | (~spl4_1 | spl4_5)),
% 1.74/0.61    inference(subsumption_resolution,[],[f355,f205])).
% 1.74/0.61  fof(f355,plain,(
% 1.74/0.61    ~v1_relat_1(sK2) | spl4_5),
% 1.74/0.61    inference(resolution,[],[f347,f132])).
% 1.74/0.61  fof(f347,plain,(
% 1.74/0.61    ~v1_relat_1(k4_relat_1(sK2)) | spl4_5),
% 1.74/0.61    inference(avatar_component_clause,[],[f345])).
% 1.74/0.61  fof(f352,plain,(
% 1.74/0.61    ~spl4_5 | spl4_6 | ~spl4_1 | ~spl4_2),
% 1.74/0.61    inference(avatar_split_clause,[],[f287,f208,f204,f349,f345])).
% 1.74/0.61  fof(f287,plain,(
% 1.74/0.61    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.61    inference(forward_demodulation,[],[f286,f147])).
% 1.74/0.61  fof(f286,plain,(
% 1.74/0.61    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.61    inference(forward_demodulation,[],[f285,f255])).
% 1.74/0.61  fof(f285,plain,(
% 1.74/0.61    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f283,f205])).
% 1.74/0.61  fof(f283,plain,(
% 1.74/0.61    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_2),
% 1.74/0.61    inference(superposition,[],[f122,f281])).
% 1.74/0.61  fof(f251,plain,(
% 1.74/0.61    spl4_1),
% 1.74/0.61    inference(avatar_contradiction_clause,[],[f250])).
% 1.74/0.61  fof(f250,plain,(
% 1.74/0.61    $false | spl4_1),
% 1.74/0.61    inference(subsumption_resolution,[],[f248,f120])).
% 1.74/0.61  fof(f248,plain,(
% 1.74/0.61    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 1.74/0.61    inference(resolution,[],[f220,f84])).
% 1.74/0.61  fof(f220,plain,(
% 1.74/0.61    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 1.74/0.61    inference(resolution,[],[f206,f119])).
% 1.74/0.61  fof(f206,plain,(
% 1.74/0.61    ~v1_relat_1(sK2) | spl4_1),
% 1.74/0.61    inference(avatar_component_clause,[],[f204])).
% 1.74/0.61  fof(f211,plain,(
% 1.74/0.61    ~spl4_1 | spl4_2),
% 1.74/0.61    inference(avatar_split_clause,[],[f161,f208,f204])).
% 1.74/0.61  fof(f161,plain,(
% 1.74/0.61    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(subsumption_resolution,[],[f157,f82])).
% 1.74/0.61  fof(f157,plain,(
% 1.74/0.61    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.74/0.61    inference(resolution,[],[f90,f102])).
% 1.74/0.61  % SZS output end Proof for theBenchmark
% 1.74/0.61  % (13070)------------------------------
% 1.74/0.61  % (13070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.61  % (13070)Termination reason: Refutation
% 1.74/0.61  
% 1.74/0.61  % (13070)Memory used [KB]: 11513
% 1.74/0.61  % (13070)Time elapsed: 0.195 s
% 1.74/0.61  % (13070)------------------------------
% 1.74/0.61  % (13070)------------------------------
% 1.74/0.61  % (13045)Success in time 0.246 s
%------------------------------------------------------------------------------
