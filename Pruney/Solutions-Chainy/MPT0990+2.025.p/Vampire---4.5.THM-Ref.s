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
% DateTime   : Thu Dec  3 13:02:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 547 expanded)
%              Number of leaves         :   58 ( 205 expanded)
%              Depth                    :   15
%              Number of atoms          : 1003 (2698 expanded)
%              Number of equality atoms :  193 ( 727 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1563,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f140,f191,f193,f200,f224,f237,f239,f248,f250,f260,f274,f284,f293,f315,f317,f334,f336,f356,f418,f496,f536,f543,f548,f564,f579,f613,f621,f867,f1337,f1430,f1436,f1443,f1453,f1470,f1472,f1489,f1553])).

fof(f1553,plain,(
    ~ spl4_33 ),
    inference(avatar_contradiction_clause,[],[f1514])).

fof(f1514,plain,
    ( $false
    | ~ spl4_33 ),
    inference(subsumption_resolution,[],[f62,f440])).

fof(f440,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl4_33
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f62,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f1489,plain,
    ( ~ spl4_20
    | spl4_33
    | ~ spl4_6
    | ~ spl4_22
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_5
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f1488,f594,f557,f280,f270,f134,f181,f308,f300,f331,f185,f438,f312])).

fof(f312,plain,
    ( spl4_20
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f185,plain,
    ( spl4_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f331,plain,
    ( spl4_22
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f300,plain,
    ( spl4_17
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f308,plain,
    ( spl4_19
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f181,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f270,plain,
    ( spl4_15
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f280,plain,
    ( spl4_16
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f557,plain,
    ( spl4_46
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f594,plain,
    ( spl4_50
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f1488,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(trivial_inequality_removal,[],[f1487])).

fof(f1487,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1486,f282])).

fof(f282,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f280])).

fof(f1486,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_46
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f1485,f596])).

fof(f596,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f594])).

fof(f1485,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(trivial_inequality_removal,[],[f1484])).

fof(f1484,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f1483,f136])).

fof(f136,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1483,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f1444,f272])).

fof(f272,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f270])).

fof(f1444,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK3 = k2_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f394,f559])).

fof(f559,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f557])).

fof(f394,plain,(
    ! [X2] :
      ( k6_partfun1(k1_relat_1(X2)) != k6_partfun1(k2_relat_1(k2_funct_1(X2)))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(k2_funct_1(X2))
      | k2_relat_1(X2) != k1_relat_1(k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X2))
      | k2_funct_1(k2_funct_1(X2)) = X2
      | ~ v2_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f392])).

fof(f392,plain,(
    ! [X2] :
      ( k6_partfun1(k1_relat_1(X2)) != k6_partfun1(k2_relat_1(k2_funct_1(X2)))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(k2_funct_1(X2))
      | k2_relat_1(X2) != k1_relat_1(k2_funct_1(X2))
      | ~ v1_relat_1(k2_funct_1(X2))
      | k2_funct_1(k2_funct_1(X2)) = X2
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f109,f108])).

fof(f108,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f77,f66])).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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

fof(f109,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f79,f66])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f1472,plain,
    ( spl4_18
    | ~ spl4_44
    | ~ spl4_85 ),
    inference(avatar_contradiction_clause,[],[f1471])).

fof(f1471,plain,
    ( $false
    | spl4_18
    | ~ spl4_44
    | ~ spl4_85 ),
    inference(subsumption_resolution,[],[f551,f860])).

fof(f860,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ spl4_85 ),
    inference(avatar_component_clause,[],[f858])).

fof(f858,plain,
    ( spl4_85
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f551,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_18
    | ~ spl4_44 ),
    inference(superposition,[],[f306,f517])).

fof(f517,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl4_44
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f306,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl4_18
  <=> v2_funct_1(k5_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1470,plain,(
    spl4_38 ),
    inference(avatar_contradiction_clause,[],[f1468])).

fof(f1468,plain,
    ( $false
    | spl4_38 ),
    inference(unit_resulting_resolution,[],[f121,f59,f63,f477,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f477,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl4_38 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl4_38
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f121,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f86,f65])).

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1453,plain,(
    spl4_154 ),
    inference(avatar_contradiction_clause,[],[f1450])).

fof(f1450,plain,
    ( $false
    | spl4_154 ),
    inference(unit_resulting_resolution,[],[f111,f1442])).

fof(f1442,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_154 ),
    inference(avatar_component_clause,[],[f1440])).

fof(f1440,plain,
    ( spl4_154
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1443,plain,
    ( ~ spl4_6
    | ~ spl4_22
    | ~ spl4_5
    | ~ spl4_154
    | ~ spl4_16
    | spl4_153 ),
    inference(avatar_split_clause,[],[f1438,f1433,f280,f1440,f181,f331,f185])).

fof(f1433,plain,
    ( spl4_153
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).

fof(f1438,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_16
    | spl4_153 ),
    inference(forward_demodulation,[],[f1437,f282])).

fof(f1437,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_153 ),
    inference(superposition,[],[f1435,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f1435,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl4_153 ),
    inference(avatar_component_clause,[],[f1433])).

fof(f1436,plain,
    ( ~ spl4_36
    | ~ spl4_153
    | ~ spl4_38
    | spl4_152 ),
    inference(avatar_split_clause,[],[f1431,f1427,f476,f1433,f468])).

fof(f468,plain,
    ( spl4_36
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f1427,plain,
    ( spl4_152
  <=> v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f1431,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_152 ),
    inference(superposition,[],[f1429,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f82,f66])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f1429,plain,
    ( ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)))
    | spl4_152 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f1430,plain,
    ( ~ spl4_45
    | ~ spl4_152
    | ~ spl4_57
    | spl4_85
    | ~ spl4_145 ),
    inference(avatar_split_clause,[],[f1425,f1335,f858,f635,f1427,f545])).

fof(f545,plain,
    ( spl4_45
  <=> v1_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f635,plain,
    ( spl4_57
  <=> v1_relat_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1335,plain,
    ( spl4_145
  <=> ! [X5] :
        ( sK0 != k1_relat_1(X5)
        | v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X5))
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).

fof(f1425,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ spl4_145 ),
    inference(equality_resolution,[],[f1359])).

fof(f1359,plain,
    ( ! [X1] :
        ( sK0 != X1
        | v2_funct_1(k6_partfun1(X1))
        | ~ v1_relat_1(k6_partfun1(X1))
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(X1)))
        | ~ v1_funct_1(k6_partfun1(X1)) )
    | ~ spl4_145 ),
    inference(superposition,[],[f1336,f106])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f66])).

fof(f68,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1336,plain,
    ( ! [X5] :
        ( sK0 != k1_relat_1(X5)
        | v2_funct_1(X5)
        | ~ v1_relat_1(X5)
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X5))
        | ~ v1_funct_1(X5) )
    | ~ spl4_145 ),
    inference(avatar_component_clause,[],[f1335])).

fof(f1337,plain,
    ( ~ spl4_6
    | ~ spl4_22
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_36
    | spl4_145
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f1313,f280,f1335,f468,f327,f181,f331,f185])).

fof(f327,plain,
    ( spl4_21
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1313,plain,
    ( ! [X5] :
        ( sK0 != k1_relat_1(X5)
        | ~ v1_funct_1(X5)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k5_relat_1(k2_funct_1(sK2),X5))
        | ~ v1_relat_1(X5)
        | v2_funct_1(X5)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_16 ),
    inference(superposition,[],[f176,f282])).

fof(f176,plain,(
    ! [X2,X3] :
      ( k1_relat_1(X2) != k1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(k5_relat_1(k2_funct_1(X2),X3))
      | ~ v1_relat_1(X3)
      | v2_funct_1(X3)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f81,f76])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f867,plain,(
    spl4_57 ),
    inference(avatar_contradiction_clause,[],[f863])).

fof(f863,plain,
    ( $false
    | spl4_57 ),
    inference(unit_resulting_resolution,[],[f104,f637,f86])).

fof(f637,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_57 ),
    inference(avatar_component_clause,[],[f635])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f66])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f621,plain,
    ( spl4_47
    | ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f620])).

fof(f620,plain,
    ( $false
    | spl4_47
    | ~ spl4_50 ),
    inference(trivial_inequality_removal,[],[f614])).

fof(f614,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_47
    | ~ spl4_50 ),
    inference(superposition,[],[f563,f596])).

fof(f563,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl4_47
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f613,plain,
    ( ~ spl4_14
    | spl4_50
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f589,f576,f594,f266])).

fof(f266,plain,
    ( spl4_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f576,plain,
    ( spl4_48
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f589,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_48 ),
    inference(superposition,[],[f88,f578])).

fof(f578,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f576])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f579,plain,
    ( spl4_48
    | ~ spl4_17
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f571,f213,f266,f181,f226,f130,f300,f576])).

fof(f130,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f226,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f213,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f571,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f98,f58])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f564,plain,
    ( spl4_46
    | ~ spl4_19
    | ~ spl4_20
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_47
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f555,f515,f270,f134,f561,f300,f185,f181,f312,f308,f557])).

fof(f555,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(trivial_inequality_removal,[],[f554])).

fof(f554,plain,
    ( sK1 != sK1
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f553,f136])).

fof(f553,plain,
    ( sK1 != k2_relat_1(sK2)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_15
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f552,f272])).

fof(f552,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_44 ),
    inference(superposition,[],[f109,f517])).

fof(f548,plain,
    ( ~ spl4_5
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_1
    | spl4_45
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f541,f353,f545,f130,f300,f266,f181])).

fof(f353,plain,
    ( spl4_24
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f541,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_24 ),
    inference(superposition,[],[f102,f355])).

fof(f355,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f353])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f543,plain,
    ( ~ spl4_5
    | ~ spl4_14
    | ~ spl4_17
    | ~ spl4_1
    | spl4_44
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f540,f353,f515,f130,f300,f266,f181])).

fof(f540,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_24 ),
    inference(superposition,[],[f101,f355])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f536,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f524])).

fof(f524,plain,
    ( $false
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f63,f54,f56,f65,f351,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f351,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl4_23
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f496,plain,(
    spl4_36 ),
    inference(avatar_contradiction_clause,[],[f493])).

fof(f493,plain,
    ( $false
    | spl4_36 ),
    inference(unit_resulting_resolution,[],[f121,f63,f470,f73])).

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f470,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_36 ),
    inference(avatar_component_clause,[],[f468])).

fof(f418,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f120,f310])).

fof(f310,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f308])).

fof(f120,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f86,f56])).

fof(f356,plain,
    ( ~ spl4_23
    | spl4_24 ),
    inference(avatar_split_clause,[],[f346,f353,f349])).

fof(f346,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f290,f58])).

fof(f290,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f100,f104])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f336,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl4_22 ),
    inference(subsumption_resolution,[],[f59,f333])).

fof(f333,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f331])).

fof(f334,plain,
    ( spl4_21
    | ~ spl4_5
    | ~ spl4_22
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f325,f226,f130,f331,f181,f327])).

fof(f325,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f95,f57])).

fof(f57,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f317,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f54,f302])).

fof(f302,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f315,plain,
    ( ~ spl4_17
    | ~ spl4_18
    | ~ spl4_19
    | spl4_20
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f298,f270,f189,f312,f308,f304,f300])).

fof(f189,plain,
    ( spl4_7
  <=> ! [X4] :
        ( sK1 != k1_relat_1(X4)
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v2_funct_1(k5_relat_1(sK2,X4))
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f298,plain,
    ( v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(trivial_inequality_removal,[],[f296])).

fof(f296,plain,
    ( sK1 != sK1
    | v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_15 ),
    inference(superposition,[],[f190,f272])).

fof(f190,plain,
    ( ! [X4] :
        ( sK1 != k1_relat_1(X4)
        | v2_funct_1(X4)
        | ~ v1_relat_1(X4)
        | ~ v2_funct_1(k5_relat_1(sK2,X4))
        | ~ v1_funct_1(X4) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f189])).

fof(f293,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl4_14 ),
    inference(subsumption_resolution,[],[f56,f268])).

fof(f268,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f266])).

fof(f284,plain,
    ( ~ spl4_1
    | spl4_16
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f277,f230,f280,f130])).

fof(f230,plain,
    ( spl4_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f277,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_12 ),
    inference(superposition,[],[f87,f232])).

fof(f232,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f230])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f274,plain,
    ( ~ spl4_14
    | spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f263,f217,f270,f266])).

fof(f217,plain,
    ( spl4_9
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f263,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_9 ),
    inference(superposition,[],[f87,f219])).

fof(f219,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f217])).

fof(f260,plain,(
    ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f61,f236])).

fof(f236,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl4_13
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f61,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f250,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f64,f228])).

fof(f228,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f226])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f248,plain,(
    ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f60,f223])).

fof(f223,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f60,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f239,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f55,f215])).

fof(f215,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f213])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f237,plain,
    ( ~ spl4_11
    | spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f211,f234,f230,f226])).

fof(f211,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f94,f65])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f224,plain,
    ( ~ spl4_8
    | spl4_9
    | spl4_10 ),
    inference(avatar_split_clause,[],[f209,f221,f217,f213])).

fof(f209,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f94,f56])).

fof(f200,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f121,f187])).

fof(f187,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f185])).

fof(f193,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f63,f183])).

fof(f183,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f181])).

fof(f191,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f177,f134,f189,f185,f181])).

fof(f177,plain,
    ( ! [X4] :
        ( sK1 != k1_relat_1(X4)
        | ~ v1_funct_1(X4)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v2_funct_1(k5_relat_1(sK2,X4))
        | ~ v1_relat_1(X4)
        | v2_funct_1(X4) )
    | ~ spl4_2 ),
    inference(superposition,[],[f81,f136])).

fof(f140,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f65,f132])).

fof(f132,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f138,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f128,f134,f130])).

fof(f128,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f57,f88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:38:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22814)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (22823)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (22813)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (22833)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (22831)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (22839)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (22824)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (22815)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22812)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (22810)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (22811)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (22835)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (22836)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (22809)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (22816)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (22829)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (22834)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (22827)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (22825)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (22832)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (22821)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (22827)Refutation not found, incomplete strategy% (22827)------------------------------
% 0.21/0.55  % (22827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22827)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22827)Memory used [KB]: 10746
% 0.21/0.55  % (22827)Time elapsed: 0.138 s
% 0.21/0.55  % (22827)------------------------------
% 0.21/0.55  % (22827)------------------------------
% 0.21/0.56  % (22828)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (22819)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (22837)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (22840)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (22822)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (22838)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (22830)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (22817)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (22818)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.57  % (22823)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 1.65/0.58  fof(f1563,plain,(
% 1.65/0.58    $false),
% 1.65/0.58    inference(avatar_sat_refutation,[],[f138,f140,f191,f193,f200,f224,f237,f239,f248,f250,f260,f274,f284,f293,f315,f317,f334,f336,f356,f418,f496,f536,f543,f548,f564,f579,f613,f621,f867,f1337,f1430,f1436,f1443,f1453,f1470,f1472,f1489,f1553])).
% 1.65/0.58  fof(f1553,plain,(
% 1.65/0.58    ~spl4_33),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1514])).
% 1.65/0.58  fof(f1514,plain,(
% 1.65/0.58    $false | ~spl4_33),
% 1.65/0.58    inference(subsumption_resolution,[],[f62,f440])).
% 1.65/0.58  fof(f440,plain,(
% 1.65/0.58    sK3 = k2_funct_1(sK2) | ~spl4_33),
% 1.65/0.58    inference(avatar_component_clause,[],[f438])).
% 1.65/0.58  fof(f438,plain,(
% 1.65/0.58    spl4_33 <=> sK3 = k2_funct_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    sK3 != k2_funct_1(sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f24,plain,(
% 1.65/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f23])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f22])).
% 1.65/0.58  fof(f22,negated_conjecture,(
% 1.65/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.65/0.58    inference(negated_conjecture,[],[f21])).
% 1.65/0.58  fof(f21,conjecture,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.65/0.58  fof(f1489,plain,(
% 1.65/0.58    ~spl4_20 | spl4_33 | ~spl4_6 | ~spl4_22 | ~spl4_17 | ~spl4_19 | ~spl4_5 | ~spl4_2 | ~spl4_15 | ~spl4_16 | ~spl4_46 | ~spl4_50),
% 1.65/0.58    inference(avatar_split_clause,[],[f1488,f594,f557,f280,f270,f134,f181,f308,f300,f331,f185,f438,f312])).
% 1.65/0.58  fof(f312,plain,(
% 1.65/0.58    spl4_20 <=> v2_funct_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.65/0.58  fof(f185,plain,(
% 1.65/0.58    spl4_6 <=> v1_relat_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.65/0.58  fof(f331,plain,(
% 1.65/0.58    spl4_22 <=> v2_funct_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.65/0.58  fof(f300,plain,(
% 1.65/0.58    spl4_17 <=> v1_funct_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.65/0.58  fof(f308,plain,(
% 1.65/0.58    spl4_19 <=> v1_relat_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.65/0.58  fof(f181,plain,(
% 1.65/0.58    spl4_5 <=> v1_funct_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.65/0.58  fof(f134,plain,(
% 1.65/0.58    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.65/0.58  fof(f270,plain,(
% 1.65/0.58    spl4_15 <=> sK1 = k1_relat_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.65/0.58  fof(f280,plain,(
% 1.65/0.58    spl4_16 <=> sK0 = k1_relat_1(sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.65/0.58  fof(f557,plain,(
% 1.65/0.58    spl4_46 <=> sK2 = k2_funct_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.65/0.58  fof(f594,plain,(
% 1.65/0.58    spl4_50 <=> sK0 = k2_relat_1(sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.65/0.58  fof(f1488,plain,(
% 1.65/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_16 | ~spl4_46 | ~spl4_50)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f1487])).
% 1.65/0.58  fof(f1487,plain,(
% 1.65/0.58    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_16 | ~spl4_46 | ~spl4_50)),
% 1.65/0.58    inference(forward_demodulation,[],[f1486,f282])).
% 1.65/0.58  fof(f282,plain,(
% 1.65/0.58    sK0 = k1_relat_1(sK2) | ~spl4_16),
% 1.65/0.58    inference(avatar_component_clause,[],[f280])).
% 1.65/0.58  fof(f1486,plain,(
% 1.65/0.58    sK0 != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_46 | ~spl4_50)),
% 1.65/0.58    inference(forward_demodulation,[],[f1485,f596])).
% 1.65/0.58  fof(f596,plain,(
% 1.65/0.58    sK0 = k2_relat_1(sK3) | ~spl4_50),
% 1.65/0.58    inference(avatar_component_clause,[],[f594])).
% 1.65/0.58  fof(f1485,plain,(
% 1.65/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_46)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f1484])).
% 1.65/0.58  fof(f1484,plain,(
% 1.65/0.58    k6_partfun1(sK1) != k6_partfun1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_46)),
% 1.65/0.58    inference(forward_demodulation,[],[f1483,f136])).
% 1.65/0.58  fof(f136,plain,(
% 1.65/0.58    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 1.65/0.58    inference(avatar_component_clause,[],[f134])).
% 1.65/0.58  fof(f1483,plain,(
% 1.65/0.58    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | (~spl4_15 | ~spl4_46)),
% 1.65/0.58    inference(forward_demodulation,[],[f1444,f272])).
% 1.65/0.58  fof(f272,plain,(
% 1.65/0.58    sK1 = k1_relat_1(sK3) | ~spl4_15),
% 1.65/0.58    inference(avatar_component_clause,[],[f270])).
% 1.65/0.58  fof(f1444,plain,(
% 1.65/0.58    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK2) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | sK3 = k2_funct_1(sK2) | ~v2_funct_1(sK3) | ~spl4_46),
% 1.65/0.58    inference(superposition,[],[f394,f559])).
% 1.65/0.58  fof(f559,plain,(
% 1.65/0.58    sK2 = k2_funct_1(sK3) | ~spl4_46),
% 1.65/0.58    inference(avatar_component_clause,[],[f557])).
% 1.65/0.58  fof(f394,plain,(
% 1.65/0.58    ( ! [X2] : (k6_partfun1(k1_relat_1(X2)) != k6_partfun1(k2_relat_1(k2_funct_1(X2))) | ~v1_funct_1(k2_funct_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(k2_funct_1(X2)) | k2_relat_1(X2) != k1_relat_1(k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X2)) | k2_funct_1(k2_funct_1(X2)) = X2 | ~v2_funct_1(X2)) )),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f392])).
% 1.65/0.58  fof(f392,plain,(
% 1.65/0.58    ( ! [X2] : (k6_partfun1(k1_relat_1(X2)) != k6_partfun1(k2_relat_1(k2_funct_1(X2))) | ~v1_funct_1(k2_funct_1(X2)) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(k2_funct_1(X2)) | k2_relat_1(X2) != k1_relat_1(k2_funct_1(X2)) | ~v1_relat_1(k2_funct_1(X2)) | k2_funct_1(k2_funct_1(X2)) = X2 | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.65/0.58    inference(superposition,[],[f109,f108])).
% 1.65/0.58  fof(f108,plain,(
% 1.65/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f77,f66])).
% 1.65/0.58  fof(f66,plain,(
% 1.65/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f18])).
% 1.65/0.58  fof(f18,axiom,(
% 1.65/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.65/0.58  fof(f77,plain,(
% 1.65/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.65/0.58  fof(f109,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.65/0.58    inference(definition_unfolding,[],[f79,f66])).
% 1.65/0.58  fof(f79,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.65/0.58  fof(f1472,plain,(
% 1.65/0.58    spl4_18 | ~spl4_44 | ~spl4_85),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1471])).
% 1.65/0.58  fof(f1471,plain,(
% 1.65/0.58    $false | (spl4_18 | ~spl4_44 | ~spl4_85)),
% 1.65/0.58    inference(subsumption_resolution,[],[f551,f860])).
% 1.65/0.58  fof(f860,plain,(
% 1.65/0.58    v2_funct_1(k6_partfun1(sK0)) | ~spl4_85),
% 1.65/0.58    inference(avatar_component_clause,[],[f858])).
% 1.65/0.58  fof(f858,plain,(
% 1.65/0.58    spl4_85 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 1.65/0.58  fof(f551,plain,(
% 1.65/0.58    ~v2_funct_1(k6_partfun1(sK0)) | (spl4_18 | ~spl4_44)),
% 1.65/0.58    inference(superposition,[],[f306,f517])).
% 1.65/0.58  fof(f517,plain,(
% 1.65/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_44),
% 1.65/0.58    inference(avatar_component_clause,[],[f515])).
% 1.65/0.58  fof(f515,plain,(
% 1.65/0.58    spl4_44 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.65/0.58  fof(f306,plain,(
% 1.65/0.58    ~v2_funct_1(k5_relat_1(sK2,sK3)) | spl4_18),
% 1.65/0.58    inference(avatar_component_clause,[],[f304])).
% 1.65/0.58  fof(f304,plain,(
% 1.65/0.58    spl4_18 <=> v2_funct_1(k5_relat_1(sK2,sK3))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.65/0.58  fof(f1470,plain,(
% 1.65/0.58    spl4_38),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1468])).
% 1.65/0.58  fof(f1468,plain,(
% 1.65/0.58    $false | spl4_38),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f121,f59,f63,f477,f72])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f25])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.65/0.58  fof(f477,plain,(
% 1.65/0.58    ~v2_funct_1(k2_funct_1(sK2)) | spl4_38),
% 1.65/0.58    inference(avatar_component_clause,[],[f476])).
% 1.65/0.58  fof(f476,plain,(
% 1.65/0.58    spl4_38 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    v1_funct_1(sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f59,plain,(
% 1.65/0.58    v2_funct_1(sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f121,plain,(
% 1.65/0.58    v1_relat_1(sK2)),
% 1.65/0.58    inference(resolution,[],[f86,f65])).
% 1.65/0.58  fof(f65,plain,(
% 1.65/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f86,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f39])).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f10])).
% 1.65/0.58  fof(f10,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.58  fof(f1453,plain,(
% 1.65/0.58    spl4_154),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f1450])).
% 1.65/0.58  fof(f1450,plain,(
% 1.65/0.58    $false | spl4_154),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f111,f1442])).
% 1.65/0.58  fof(f1442,plain,(
% 1.65/0.58    ~r1_tarski(sK0,sK0) | spl4_154),
% 1.65/0.58    inference(avatar_component_clause,[],[f1440])).
% 1.65/0.58  fof(f1440,plain,(
% 1.65/0.58    spl4_154 <=> r1_tarski(sK0,sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).
% 1.65/0.58  fof(f111,plain,(
% 1.65/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f84])).
% 1.65/0.58  fof(f84,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.58  fof(f1443,plain,(
% 1.65/0.58    ~spl4_6 | ~spl4_22 | ~spl4_5 | ~spl4_154 | ~spl4_16 | spl4_153),
% 1.65/0.58    inference(avatar_split_clause,[],[f1438,f1433,f280,f1440,f181,f331,f185])).
% 1.65/0.58  fof(f1433,plain,(
% 1.65/0.58    spl4_153 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_153])])).
% 1.65/0.58  fof(f1438,plain,(
% 1.65/0.58    ~r1_tarski(sK0,sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_16 | spl4_153)),
% 1.65/0.58    inference(forward_demodulation,[],[f1437,f282])).
% 1.65/0.58  fof(f1437,plain,(
% 1.65/0.58    ~r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_153),
% 1.65/0.58    inference(superposition,[],[f1435,f76])).
% 1.65/0.58  fof(f76,plain,(
% 1.65/0.58    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f30])).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.65/0.58  fof(f1435,plain,(
% 1.65/0.58    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl4_153),
% 1.65/0.58    inference(avatar_component_clause,[],[f1433])).
% 1.65/0.58  fof(f1436,plain,(
% 1.65/0.58    ~spl4_36 | ~spl4_153 | ~spl4_38 | spl4_152),
% 1.65/0.58    inference(avatar_split_clause,[],[f1431,f1427,f476,f1433,f468])).
% 1.65/0.58  fof(f468,plain,(
% 1.65/0.58    spl4_36 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.65/0.58  fof(f1427,plain,(
% 1.65/0.58    spl4_152 <=> v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).
% 1.65/0.58  fof(f1431,plain,(
% 1.65/0.58    ~v2_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | spl4_152),
% 1.65/0.58    inference(superposition,[],[f1429,f110])).
% 1.65/0.58  fof(f110,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(definition_unfolding,[],[f82,f66])).
% 1.65/0.58  fof(f82,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f38])).
% 1.65/0.58  fof(f38,plain,(
% 1.65/0.58    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(flattening,[],[f37])).
% 1.65/0.58  fof(f37,plain,(
% 1.65/0.58    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.65/0.58  fof(f1429,plain,(
% 1.65/0.58    ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))) | spl4_152),
% 1.65/0.58    inference(avatar_component_clause,[],[f1427])).
% 1.65/0.58  fof(f1430,plain,(
% 1.65/0.58    ~spl4_45 | ~spl4_152 | ~spl4_57 | spl4_85 | ~spl4_145),
% 1.65/0.58    inference(avatar_split_clause,[],[f1425,f1335,f858,f635,f1427,f545])).
% 1.65/0.58  fof(f545,plain,(
% 1.65/0.58    spl4_45 <=> v1_funct_1(k6_partfun1(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.65/0.58  fof(f635,plain,(
% 1.65/0.58    spl4_57 <=> v1_relat_1(k6_partfun1(sK0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.65/0.58  fof(f1335,plain,(
% 1.65/0.58    spl4_145 <=> ! [X5] : (sK0 != k1_relat_1(X5) | v2_funct_1(X5) | ~v1_relat_1(X5) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X5)) | ~v1_funct_1(X5))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_145])])).
% 1.65/0.58  fof(f1425,plain,(
% 1.65/0.58    v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k6_partfun1(sK0)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))) | ~v1_funct_1(k6_partfun1(sK0)) | ~spl4_145),
% 1.65/0.58    inference(equality_resolution,[],[f1359])).
% 1.65/0.58  fof(f1359,plain,(
% 1.65/0.58    ( ! [X1] : (sK0 != X1 | v2_funct_1(k6_partfun1(X1)) | ~v1_relat_1(k6_partfun1(X1)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),k6_partfun1(X1))) | ~v1_funct_1(k6_partfun1(X1))) ) | ~spl4_145),
% 1.65/0.58    inference(superposition,[],[f1336,f106])).
% 1.65/0.58  fof(f106,plain,(
% 1.65/0.58    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.65/0.58    inference(definition_unfolding,[],[f68,f66])).
% 1.65/0.58  fof(f68,plain,(
% 1.65/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.65/0.58    inference(cnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.65/0.58  fof(f1336,plain,(
% 1.65/0.58    ( ! [X5] : (sK0 != k1_relat_1(X5) | v2_funct_1(X5) | ~v1_relat_1(X5) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X5)) | ~v1_funct_1(X5)) ) | ~spl4_145),
% 1.65/0.58    inference(avatar_component_clause,[],[f1335])).
% 1.65/0.58  fof(f1337,plain,(
% 1.65/0.58    ~spl4_6 | ~spl4_22 | ~spl4_5 | ~spl4_21 | ~spl4_36 | spl4_145 | ~spl4_16),
% 1.65/0.58    inference(avatar_split_clause,[],[f1313,f280,f1335,f468,f327,f181,f331,f185])).
% 1.65/0.58  fof(f327,plain,(
% 1.65/0.58    spl4_21 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.65/0.58  fof(f1313,plain,(
% 1.65/0.58    ( ! [X5] : (sK0 != k1_relat_1(X5) | ~v1_funct_1(X5) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(sK2),X5)) | ~v1_relat_1(X5) | v2_funct_1(X5) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_16),
% 1.65/0.58    inference(superposition,[],[f176,f282])).
% 1.65/0.58  fof(f176,plain,(
% 1.65/0.58    ( ! [X2,X3] : (k1_relat_1(X2) != k1_relat_1(X3) | ~v1_funct_1(X3) | ~v1_relat_1(k2_funct_1(X2)) | ~v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(k5_relat_1(k2_funct_1(X2),X3)) | ~v1_relat_1(X3) | v2_funct_1(X3) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.65/0.58    inference(superposition,[],[f81,f76])).
% 1.65/0.58  fof(f81,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f36])).
% 1.65/0.58  fof(f36,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f35])).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f6])).
% 1.65/0.58  fof(f6,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.65/0.58  fof(f867,plain,(
% 1.65/0.58    spl4_57),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f863])).
% 1.65/0.58  fof(f863,plain,(
% 1.65/0.58    $false | spl4_57),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f104,f637,f86])).
% 1.65/0.58  fof(f637,plain,(
% 1.65/0.58    ~v1_relat_1(k6_partfun1(sK0)) | spl4_57),
% 1.65/0.58    inference(avatar_component_clause,[],[f635])).
% 1.65/0.58  fof(f104,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.65/0.58    inference(definition_unfolding,[],[f67,f66])).
% 1.65/0.58  fof(f67,plain,(
% 1.65/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,axiom,(
% 1.65/0.58    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.65/0.58  fof(f621,plain,(
% 1.65/0.58    spl4_47 | ~spl4_50),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f620])).
% 1.65/0.58  fof(f620,plain,(
% 1.65/0.58    $false | (spl4_47 | ~spl4_50)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f614])).
% 1.65/0.58  fof(f614,plain,(
% 1.65/0.58    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_47 | ~spl4_50)),
% 1.65/0.58    inference(superposition,[],[f563,f596])).
% 1.65/0.58  fof(f563,plain,(
% 1.65/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_47),
% 1.65/0.58    inference(avatar_component_clause,[],[f561])).
% 1.65/0.58  fof(f561,plain,(
% 1.65/0.58    spl4_47 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.65/0.58  fof(f613,plain,(
% 1.65/0.58    ~spl4_14 | spl4_50 | ~spl4_48),
% 1.65/0.58    inference(avatar_split_clause,[],[f589,f576,f594,f266])).
% 1.65/0.58  fof(f266,plain,(
% 1.65/0.58    spl4_14 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.65/0.58  fof(f576,plain,(
% 1.65/0.58    spl4_48 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 1.65/0.58  fof(f589,plain,(
% 1.65/0.58    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_48),
% 1.65/0.58    inference(superposition,[],[f88,f578])).
% 1.65/0.58  fof(f578,plain,(
% 1.65/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_48),
% 1.65/0.58    inference(avatar_component_clause,[],[f576])).
% 1.65/0.58  fof(f88,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f41])).
% 1.65/0.58  fof(f41,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f12])).
% 1.65/0.58  fof(f12,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.65/0.58  fof(f579,plain,(
% 1.65/0.58    spl4_48 | ~spl4_17 | ~spl4_1 | ~spl4_11 | ~spl4_5 | ~spl4_14 | ~spl4_8),
% 1.65/0.58    inference(avatar_split_clause,[],[f571,f213,f266,f181,f226,f130,f300,f576])).
% 1.65/0.58  fof(f130,plain,(
% 1.65/0.58    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.65/0.58  fof(f226,plain,(
% 1.65/0.58    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.65/0.58  fof(f213,plain,(
% 1.65/0.58    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.65/0.58  fof(f571,plain,(
% 1.65/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.65/0.58    inference(resolution,[],[f98,f58])).
% 1.65/0.58  fof(f58,plain,(
% 1.65/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f98,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f47])).
% 1.65/0.58  fof(f47,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f46])).
% 1.65/0.58  fof(f46,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.65/0.58  fof(f564,plain,(
% 1.65/0.58    spl4_46 | ~spl4_19 | ~spl4_20 | ~spl4_5 | ~spl4_6 | ~spl4_17 | ~spl4_47 | ~spl4_2 | ~spl4_15 | ~spl4_44),
% 1.65/0.58    inference(avatar_split_clause,[],[f555,f515,f270,f134,f561,f300,f185,f181,f312,f308,f557])).
% 1.65/0.58  fof(f555,plain,(
% 1.65/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_44)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f554])).
% 1.65/0.58  fof(f554,plain,(
% 1.65/0.58    sK1 != sK1 | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_2 | ~spl4_15 | ~spl4_44)),
% 1.65/0.58    inference(forward_demodulation,[],[f553,f136])).
% 1.65/0.58  fof(f553,plain,(
% 1.65/0.58    sK1 != k2_relat_1(sK2) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_15 | ~spl4_44)),
% 1.65/0.58    inference(forward_demodulation,[],[f552,f272])).
% 1.65/0.58  fof(f552,plain,(
% 1.65/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_44),
% 1.65/0.58    inference(superposition,[],[f109,f517])).
% 1.65/0.58  fof(f548,plain,(
% 1.65/0.58    ~spl4_5 | ~spl4_14 | ~spl4_17 | ~spl4_1 | spl4_45 | ~spl4_24),
% 1.65/0.58    inference(avatar_split_clause,[],[f541,f353,f545,f130,f300,f266,f181])).
% 1.65/0.58  fof(f353,plain,(
% 1.65/0.58    spl4_24 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.65/0.58  fof(f541,plain,(
% 1.65/0.58    v1_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_24),
% 1.65/0.58    inference(superposition,[],[f102,f355])).
% 1.65/0.58  fof(f355,plain,(
% 1.65/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_24),
% 1.65/0.58    inference(avatar_component_clause,[],[f353])).
% 1.65/0.58  fof(f102,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f53])).
% 1.65/0.58  fof(f53,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.65/0.58    inference(flattening,[],[f52])).
% 1.65/0.58  fof(f52,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.65/0.58    inference(ennf_transformation,[],[f16])).
% 1.65/0.58  fof(f16,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.65/0.58  fof(f543,plain,(
% 1.65/0.58    ~spl4_5 | ~spl4_14 | ~spl4_17 | ~spl4_1 | spl4_44 | ~spl4_24),
% 1.65/0.58    inference(avatar_split_clause,[],[f540,f353,f515,f130,f300,f266,f181])).
% 1.65/0.58  fof(f540,plain,(
% 1.65/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_24),
% 1.65/0.58    inference(superposition,[],[f101,f355])).
% 1.65/0.58  fof(f101,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f51,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.65/0.58    inference(flattening,[],[f50])).
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.65/0.58    inference(ennf_transformation,[],[f17])).
% 1.65/0.58  fof(f17,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.65/0.58  fof(f536,plain,(
% 1.65/0.58    spl4_23),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f524])).
% 1.65/0.58  fof(f524,plain,(
% 1.65/0.58    $false | spl4_23),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f63,f54,f56,f65,f351,f103])).
% 1.65/0.58  fof(f103,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f53])).
% 1.65/0.58  fof(f351,plain,(
% 1.65/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_23),
% 1.65/0.58    inference(avatar_component_clause,[],[f349])).
% 1.65/0.58  fof(f349,plain,(
% 1.65/0.58    spl4_23 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.65/0.58  fof(f56,plain,(
% 1.65/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f54,plain,(
% 1.65/0.58    v1_funct_1(sK3)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f496,plain,(
% 1.65/0.58    spl4_36),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f493])).
% 1.65/0.58  fof(f493,plain,(
% 1.65/0.58    $false | spl4_36),
% 1.65/0.58    inference(unit_resulting_resolution,[],[f121,f63,f470,f73])).
% 1.65/0.58  fof(f73,plain,(
% 1.65/0.58    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.65/0.58    inference(flattening,[],[f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.65/0.58  fof(f470,plain,(
% 1.65/0.58    ~v1_relat_1(k2_funct_1(sK2)) | spl4_36),
% 1.65/0.58    inference(avatar_component_clause,[],[f468])).
% 1.65/0.58  fof(f418,plain,(
% 1.65/0.58    spl4_19),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f415])).
% 1.65/0.58  fof(f415,plain,(
% 1.65/0.58    $false | spl4_19),
% 1.65/0.58    inference(subsumption_resolution,[],[f120,f310])).
% 1.65/0.58  fof(f310,plain,(
% 1.65/0.58    ~v1_relat_1(sK3) | spl4_19),
% 1.65/0.58    inference(avatar_component_clause,[],[f308])).
% 1.65/0.58  fof(f120,plain,(
% 1.65/0.58    v1_relat_1(sK3)),
% 1.65/0.58    inference(resolution,[],[f86,f56])).
% 1.65/0.58  fof(f356,plain,(
% 1.65/0.58    ~spl4_23 | spl4_24),
% 1.65/0.58    inference(avatar_split_clause,[],[f346,f353,f349])).
% 1.65/0.58  fof(f346,plain,(
% 1.65/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.65/0.58    inference(resolution,[],[f290,f58])).
% 1.65/0.58  fof(f290,plain,(
% 1.65/0.58    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.65/0.58    inference(resolution,[],[f100,f104])).
% 1.65/0.58  fof(f100,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f49])).
% 1.65/0.58  fof(f49,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(flattening,[],[f48])).
% 1.65/0.58  fof(f48,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.65/0.58    inference(ennf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.65/0.58  fof(f336,plain,(
% 1.65/0.58    spl4_22),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f335])).
% 1.65/0.58  fof(f335,plain,(
% 1.65/0.58    $false | spl4_22),
% 1.65/0.58    inference(subsumption_resolution,[],[f59,f333])).
% 1.65/0.58  fof(f333,plain,(
% 1.65/0.58    ~v2_funct_1(sK2) | spl4_22),
% 1.65/0.58    inference(avatar_component_clause,[],[f331])).
% 1.65/0.58  fof(f334,plain,(
% 1.65/0.58    spl4_21 | ~spl4_5 | ~spl4_22 | ~spl4_1 | ~spl4_11),
% 1.65/0.58    inference(avatar_split_clause,[],[f325,f226,f130,f331,f181,f327])).
% 1.65/0.58  fof(f325,plain,(
% 1.65/0.58    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f322])).
% 1.65/0.58  fof(f322,plain,(
% 1.65/0.58    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.65/0.58    inference(superposition,[],[f95,f57])).
% 1.65/0.58  fof(f57,plain,(
% 1.65/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f95,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | v1_funct_1(k2_funct_1(X2))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f45])).
% 1.65/0.58  fof(f45,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f20])).
% 1.65/0.58  fof(f20,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.65/0.58  fof(f317,plain,(
% 1.65/0.58    spl4_17),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f316])).
% 1.65/0.58  fof(f316,plain,(
% 1.65/0.58    $false | spl4_17),
% 1.65/0.58    inference(subsumption_resolution,[],[f54,f302])).
% 1.65/0.58  fof(f302,plain,(
% 1.65/0.58    ~v1_funct_1(sK3) | spl4_17),
% 1.65/0.58    inference(avatar_component_clause,[],[f300])).
% 1.65/0.58  fof(f315,plain,(
% 1.65/0.58    ~spl4_17 | ~spl4_18 | ~spl4_19 | spl4_20 | ~spl4_7 | ~spl4_15),
% 1.65/0.58    inference(avatar_split_clause,[],[f298,f270,f189,f312,f308,f304,f300])).
% 1.65/0.58  fof(f189,plain,(
% 1.65/0.58    spl4_7 <=> ! [X4] : (sK1 != k1_relat_1(X4) | v2_funct_1(X4) | ~v1_relat_1(X4) | ~v2_funct_1(k5_relat_1(sK2,X4)) | ~v1_funct_1(X4))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.65/0.58  fof(f298,plain,(
% 1.65/0.58    v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_15)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f296])).
% 1.65/0.58  fof(f296,plain,(
% 1.65/0.58    sK1 != sK1 | v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_15)),
% 1.65/0.58    inference(superposition,[],[f190,f272])).
% 1.65/0.58  fof(f190,plain,(
% 1.65/0.58    ( ! [X4] : (sK1 != k1_relat_1(X4) | v2_funct_1(X4) | ~v1_relat_1(X4) | ~v2_funct_1(k5_relat_1(sK2,X4)) | ~v1_funct_1(X4)) ) | ~spl4_7),
% 1.65/0.58    inference(avatar_component_clause,[],[f189])).
% 1.65/0.58  fof(f293,plain,(
% 1.65/0.58    spl4_14),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f292])).
% 1.65/0.58  fof(f292,plain,(
% 1.65/0.58    $false | spl4_14),
% 1.65/0.58    inference(subsumption_resolution,[],[f56,f268])).
% 1.65/0.58  fof(f268,plain,(
% 1.65/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_14),
% 1.65/0.58    inference(avatar_component_clause,[],[f266])).
% 1.65/0.58  fof(f284,plain,(
% 1.65/0.58    ~spl4_1 | spl4_16 | ~spl4_12),
% 1.65/0.58    inference(avatar_split_clause,[],[f277,f230,f280,f130])).
% 1.65/0.58  fof(f230,plain,(
% 1.65/0.58    spl4_12 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.65/0.58  fof(f277,plain,(
% 1.65/0.58    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_12),
% 1.65/0.58    inference(superposition,[],[f87,f232])).
% 1.65/0.58  fof(f232,plain,(
% 1.65/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_12),
% 1.65/0.58    inference(avatar_component_clause,[],[f230])).
% 1.65/0.58  fof(f87,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f40])).
% 1.65/0.58  fof(f40,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f11])).
% 1.65/0.58  fof(f11,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.65/0.58  fof(f274,plain,(
% 1.65/0.58    ~spl4_14 | spl4_15 | ~spl4_9),
% 1.65/0.58    inference(avatar_split_clause,[],[f263,f217,f270,f266])).
% 1.65/0.58  fof(f217,plain,(
% 1.65/0.58    spl4_9 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.65/0.58  fof(f263,plain,(
% 1.65/0.58    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_9),
% 1.65/0.58    inference(superposition,[],[f87,f219])).
% 1.65/0.58  fof(f219,plain,(
% 1.65/0.58    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl4_9),
% 1.65/0.58    inference(avatar_component_clause,[],[f217])).
% 1.65/0.58  fof(f260,plain,(
% 1.65/0.58    ~spl4_13),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f251])).
% 1.65/0.58  fof(f251,plain,(
% 1.65/0.58    $false | ~spl4_13),
% 1.65/0.58    inference(subsumption_resolution,[],[f61,f236])).
% 1.65/0.58  fof(f236,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | ~spl4_13),
% 1.65/0.58    inference(avatar_component_clause,[],[f234])).
% 1.65/0.58  fof(f234,plain,(
% 1.65/0.58    spl4_13 <=> k1_xboole_0 = sK1),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    k1_xboole_0 != sK1),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f250,plain,(
% 1.65/0.58    spl4_11),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f249])).
% 1.65/0.58  fof(f249,plain,(
% 1.65/0.58    $false | spl4_11),
% 1.65/0.58    inference(subsumption_resolution,[],[f64,f228])).
% 1.65/0.58  fof(f228,plain,(
% 1.65/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl4_11),
% 1.65/0.58    inference(avatar_component_clause,[],[f226])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f248,plain,(
% 1.65/0.58    ~spl4_10),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f240])).
% 1.65/0.58  fof(f240,plain,(
% 1.65/0.58    $false | ~spl4_10),
% 1.65/0.58    inference(subsumption_resolution,[],[f60,f223])).
% 1.65/0.58  fof(f223,plain,(
% 1.65/0.58    k1_xboole_0 = sK0 | ~spl4_10),
% 1.65/0.58    inference(avatar_component_clause,[],[f221])).
% 1.65/0.58  fof(f221,plain,(
% 1.65/0.58    spl4_10 <=> k1_xboole_0 = sK0),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    k1_xboole_0 != sK0),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f239,plain,(
% 1.65/0.58    spl4_8),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f238])).
% 1.65/0.58  fof(f238,plain,(
% 1.65/0.58    $false | spl4_8),
% 1.65/0.58    inference(subsumption_resolution,[],[f55,f215])).
% 1.65/0.58  fof(f215,plain,(
% 1.65/0.58    ~v1_funct_2(sK3,sK1,sK0) | spl4_8),
% 1.65/0.58    inference(avatar_component_clause,[],[f213])).
% 1.65/0.58  fof(f55,plain,(
% 1.65/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f237,plain,(
% 1.65/0.58    ~spl4_11 | spl4_12 | spl4_13),
% 1.65/0.58    inference(avatar_split_clause,[],[f211,f234,f230,f226])).
% 1.65/0.58  fof(f211,plain,(
% 1.65/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.65/0.58    inference(resolution,[],[f94,f65])).
% 1.65/0.58  fof(f94,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f43])).
% 1.65/0.58  fof(f43,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(flattening,[],[f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.65/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.65/0.58  fof(f224,plain,(
% 1.65/0.58    ~spl4_8 | spl4_9 | spl4_10),
% 1.65/0.58    inference(avatar_split_clause,[],[f209,f221,f217,f213])).
% 1.65/0.58  fof(f209,plain,(
% 1.65/0.58    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.65/0.58    inference(resolution,[],[f94,f56])).
% 1.65/0.58  fof(f200,plain,(
% 1.65/0.58    spl4_6),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f197])).
% 1.65/0.58  fof(f197,plain,(
% 1.65/0.58    $false | spl4_6),
% 1.65/0.58    inference(subsumption_resolution,[],[f121,f187])).
% 1.65/0.58  fof(f187,plain,(
% 1.65/0.58    ~v1_relat_1(sK2) | spl4_6),
% 1.65/0.58    inference(avatar_component_clause,[],[f185])).
% 1.65/0.58  fof(f193,plain,(
% 1.65/0.58    spl4_5),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f192])).
% 1.65/0.58  fof(f192,plain,(
% 1.65/0.58    $false | spl4_5),
% 1.65/0.58    inference(subsumption_resolution,[],[f63,f183])).
% 1.65/0.58  fof(f183,plain,(
% 1.65/0.58    ~v1_funct_1(sK2) | spl4_5),
% 1.65/0.58    inference(avatar_component_clause,[],[f181])).
% 1.65/0.58  fof(f191,plain,(
% 1.65/0.58    ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_2),
% 1.65/0.58    inference(avatar_split_clause,[],[f177,f134,f189,f185,f181])).
% 1.65/0.58  fof(f177,plain,(
% 1.65/0.58    ( ! [X4] : (sK1 != k1_relat_1(X4) | ~v1_funct_1(X4) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,X4)) | ~v1_relat_1(X4) | v2_funct_1(X4)) ) | ~spl4_2),
% 1.65/0.58    inference(superposition,[],[f81,f136])).
% 1.65/0.59  fof(f140,plain,(
% 1.65/0.59    spl4_1),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f139])).
% 1.65/0.59  fof(f139,plain,(
% 1.65/0.59    $false | spl4_1),
% 1.65/0.59    inference(subsumption_resolution,[],[f65,f132])).
% 1.65/0.59  fof(f132,plain,(
% 1.65/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 1.65/0.59    inference(avatar_component_clause,[],[f130])).
% 1.65/0.59  fof(f138,plain,(
% 1.65/0.59    ~spl4_1 | spl4_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f128,f134,f130])).
% 1.65/0.59  fof(f128,plain,(
% 1.65/0.59    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.59    inference(superposition,[],[f57,f88])).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (22823)------------------------------
% 1.65/0.59  % (22823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (22823)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (22823)Memory used [KB]: 7675
% 1.65/0.59  % (22823)Time elapsed: 0.146 s
% 1.65/0.59  % (22823)------------------------------
% 1.65/0.59  % (22823)------------------------------
% 1.65/0.59  % (22803)Success in time 0.22 s
%------------------------------------------------------------------------------
