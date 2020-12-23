%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t148_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:32 EDT 2019

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  406 (1280 expanded)
%              Number of leaves         :   76 ( 455 expanded)
%              Depth                    :   22
%              Number of atoms          : 1641 (5331 expanded)
%              Number of equality atoms :  142 (1025 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1968,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f104,f111,f118,f134,f144,f155,f165,f203,f232,f251,f300,f342,f355,f356,f472,f497,f512,f606,f664,f676,f707,f795,f852,f882,f933,f1071,f1074,f1093,f1100,f1107,f1114,f1121,f1128,f1135,f1142,f1149,f1164,f1177,f1293,f1336,f1346,f1370,f1438,f1513,f1564,f1631,f1643,f1746,f1753,f1760,f1767,f1777,f1781,f1826,f1840,f1948,f1967])).

fof(f1967,plain,
    ( ~ spl6_0
    | ~ spl6_34
    | spl6_91 ),
    inference(avatar_contradiction_clause,[],[f1966])).

fof(f1966,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_34
    | ~ spl6_91 ),
    inference(subsumption_resolution,[],[f1965,f90])).

fof(f90,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1965,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_34
    | ~ spl6_91 ),
    inference(subsumption_resolution,[],[f1963,f341])).

fof(f341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl6_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1963,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_91 ),
    inference(resolution,[],[f1434,f82])).

fof(f82,plain,(
    ! [X2,X1] :
      ( v1_funct_2(sK4(k1_xboole_0,X1,X2),k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_funct_2(sK4(X0,X1,X2),X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ? [X4] :
                  ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t136_funct_2)).

fof(f1434,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f1433])).

fof(f1433,plain,
    ( spl6_91
  <=> ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f1948,plain,
    ( ~ spl6_91
    | ~ spl6_2
    | ~ spl6_4
    | spl6_65 ),
    inference(avatar_split_clause,[],[f1805,f793,f99,f96,f1433])).

fof(f96,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f99,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f793,plain,
    ( spl6_65
  <=> ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f1805,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f1804,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f1804,plain,
    ( ~ v1_funct_2(sK4(sK0,k1_xboole_0,sK2),sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f794,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f794,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_65 ),
    inference(avatar_component_clause,[],[f793])).

fof(f1840,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_86 ),
    inference(avatar_contradiction_clause,[],[f1839])).

fof(f1839,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f1838,f90])).

fof(f1838,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_86 ),
    inference(subsumption_resolution,[],[f1836,f341])).

fof(f1836,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_86 ),
    inference(resolution,[],[f1342,f1305])).

fof(f1305,plain,
    ( ! [X13] :
        ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X13) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f1304,f82])).

fof(f1304,plain,
    ( ! [X13] :
        ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,X13),k1_xboole_0,k1_xboole_0)
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X13) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f1299,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | v1_funct_1(sK4(k1_xboole_0,X1,X2)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | v1_funct_1(sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1299,plain,
    ( ! [X13] :
        ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,X13),k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X13) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f1284,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK4(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1284,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X3,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f1283,f97])).

fof(f1283,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,sK0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f1282,f100])).

fof(f1282,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X3,sK0,sK1)
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f1281,f97])).

fof(f1281,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | ~ v1_funct_2(X3,sK0,sK1)
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f48,f100])).

fof(f48,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X3,sK0,sK1)
      | ~ v1_funct_1(X3)
      | ~ r1_partfun1(sK2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ~ ( ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ~ r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t148_funct_2)).

fof(f1342,plain,
    ( r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_86 ),
    inference(avatar_component_clause,[],[f1341])).

fof(f1341,plain,
    ( spl6_86
  <=> r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_86])])).

fof(f1826,plain,
    ( spl6_86
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_60 ),
    inference(avatar_split_clause,[],[f1785,f781,f99,f96,f1341])).

fof(f781,plain,
    ( spl6_60
  <=> r1_partfun1(sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1785,plain,
    ( r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f1784,f97])).

fof(f1784,plain,
    ( r1_partfun1(sK2,sK4(sK0,k1_xboole_0,sK2))
    | ~ spl6_4
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f782,f100])).

fof(f782,plain,
    ( r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f781])).

fof(f1781,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_90
    | ~ spl6_96
    | ~ spl6_102 ),
    inference(avatar_contradiction_clause,[],[f1780])).

fof(f1780,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_90
    | ~ spl6_96
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1779,f1775])).

fof(f1775,plain,
    ( r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_90
    | ~ spl6_96
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1774,f90])).

fof(f1774,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_90
    | ~ spl6_96
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1773,f1627])).

fof(f1627,plain,
    ( m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_96 ),
    inference(avatar_component_clause,[],[f1626])).

fof(f1626,plain,
    ( spl6_96
  <=> m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_96])])).

fof(f1773,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_90
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1772,f1437])).

fof(f1437,plain,
    ( v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl6_90 ),
    inference(avatar_component_clause,[],[f1436])).

fof(f1436,plain,
    ( spl6_90
  <=> v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_90])])).

fof(f1772,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1771,f1113])).

fof(f1113,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_70 ),
    inference(avatar_component_clause,[],[f1112])).

fof(f1112,plain,
    ( spl6_70
  <=> v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_70])])).

fof(f1771,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_34
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1770,f341])).

fof(f1770,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_102 ),
    inference(trivial_inequality_removal,[],[f1768])).

fof(f1768,plain,
    ( k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) != k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_102 ),
    inference(superposition,[],[f78,f1759])).

fof(f1759,plain,
    ( k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_102 ),
    inference(avatar_component_clause,[],[f1758])).

fof(f1758,plain,
    ( spl6_102
  <=> k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_102])])).

fof(f78,plain,(
    ! [X2,X3,X1] :
      ( k1_funct_1(X2,sK3(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X3,sK3(k1_xboole_0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_funct_1(X2,sK3(X0,X1,X2,X3)) != k1_funct_1(X3,sK3(X0,X1,X2,X3))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t145_funct_2)).

fof(f1779,plain,
    ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_70
    | ~ spl6_90
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f1778,f1113])).

fof(f1778,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_90
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f1675,f1437])).

fof(f1675,plain,
    ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_96 ),
    inference(resolution,[],[f1627,f1284])).

fof(f1777,plain,
    ( ~ spl6_0
    | ~ spl6_34
    | ~ spl6_70
    | spl6_87
    | ~ spl6_90
    | ~ spl6_96
    | ~ spl6_102 ),
    inference(avatar_contradiction_clause,[],[f1776])).

fof(f1776,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_34
    | ~ spl6_70
    | ~ spl6_87
    | ~ spl6_90
    | ~ spl6_96
    | ~ spl6_102 ),
    inference(subsumption_resolution,[],[f1775,f1345])).

fof(f1345,plain,
    ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1344,plain,
    ( spl6_87
  <=> ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f1767,plain,
    ( spl6_104
    | ~ spl6_70
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f1706,f1626,f1112,f1765])).

fof(f1765,plain,
    ( spl6_104
  <=> v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK4(k1_xboole_0,k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1706,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_70
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f1677,f1113])).

fof(f1677,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_96 ),
    inference(resolution,[],[f1627,f177])).

fof(f177,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | v1_relat_1(sK4(k1_xboole_0,X5,X4)) ) ),
    inference(resolution,[],[f81,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',cc1_relset_1)).

fof(f1760,plain,
    ( spl6_102
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f1334,f340,f99,f96,f89,f1758])).

fof(f1334,plain,
    ( k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1325,f90])).

fof(f1325,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(resolution,[],[f1313,f341])).

fof(f1313,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1312,f341])).

fof(f1312,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f1311,f90])).

fof(f1311,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(duplicate_literal_removal,[],[f1306])).

fof(f1306,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(resolution,[],[f1305,f388])).

fof(f388,plain,(
    ! [X6,X4,X5] :
      ( r1_partfun1(X6,sK4(k1_xboole_0,X4,X5))
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | k1_funct_1(X6,sK3(k1_xboole_0,X4,X6,sK4(k1_xboole_0,X4,X5))) = k1_funct_1(sK4(k1_xboole_0,X4,X6),sK3(k1_xboole_0,X4,X6,sK4(k1_xboole_0,X4,X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f387,f82])).

fof(f387,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_2(sK4(k1_xboole_0,X4,X5),k1_xboole_0,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | ~ v1_funct_1(X6)
      | r1_partfun1(X6,sK4(k1_xboole_0,X4,X5))
      | k1_funct_1(X6,sK3(k1_xboole_0,X4,X6,sK4(k1_xboole_0,X4,X5))) = k1_funct_1(sK4(k1_xboole_0,X4,X6),sK3(k1_xboole_0,X4,X6,sK4(k1_xboole_0,X4,X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f384,f83])).

fof(f384,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_1(sK4(k1_xboole_0,X4,X5))
      | ~ v1_funct_2(sK4(k1_xboole_0,X4,X5),k1_xboole_0,X4)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | ~ v1_funct_1(X6)
      | r1_partfun1(X6,sK4(k1_xboole_0,X4,X5))
      | k1_funct_1(X6,sK3(k1_xboole_0,X4,X6,sK4(k1_xboole_0,X4,X5))) = k1_funct_1(sK4(k1_xboole_0,X4,X6),sK3(k1_xboole_0,X4,X6,sK4(k1_xboole_0,X4,X5)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f196,f81])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | r1_partfun1(X0,X2)
      | k1_funct_1(X0,sK3(k1_xboole_0,X1,X0,X2)) = k1_funct_1(sK4(k1_xboole_0,X1,X0),sK3(k1_xboole_0,X1,X0,X2)) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | r1_partfun1(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK3(k1_xboole_0,X1,X0,X2)) = k1_funct_1(sK4(k1_xboole_0,X1,X0),sK3(k1_xboole_0,X1,X0,X2)) ) ),
    inference(resolution,[],[f79,f84])).

fof(f84,plain,(
    ! [X4,X2,X1] :
      ( ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X4) = k1_funct_1(sK4(k1_xboole_0,X1,X2),X4) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(sK4(X0,X1,X2),X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(sK3(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | r2_hidden(sK3(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1753,plain,
    ( ~ spl6_101
    | ~ spl6_2
    | ~ spl6_4
    | spl6_43 ),
    inference(avatar_split_clause,[],[f1254,f464,f99,f96,f1751])).

fof(f1751,plain,
    ( spl6_101
  <=> ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_101])])).

fof(f464,plain,
    ( spl6_43
  <=> ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f1254,plain,
    ( ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))),k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f1253,f97])).

fof(f1253,plain,
    ( ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))),sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_43 ),
    inference(forward_demodulation,[],[f465,f100])).

fof(f465,plain,
    ( ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1)
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f464])).

fof(f1746,plain,
    ( spl6_98
    | ~ spl6_70
    | ~ spl6_96 ),
    inference(avatar_split_clause,[],[f1705,f1626,f1112,f1744])).

fof(f1744,plain,
    ( spl6_98
  <=> v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK4(k1_xboole_0,k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f1705,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_70
    | ~ spl6_96 ),
    inference(subsumption_resolution,[],[f1676,f1113])).

fof(f1676,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_96 ),
    inference(resolution,[],[f1627,f83])).

fof(f1643,plain,
    ( ~ spl6_0
    | ~ spl6_34
    | spl6_97 ),
    inference(avatar_contradiction_clause,[],[f1642])).

fof(f1642,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_34
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f1641,f90])).

fof(f1641,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_34
    | ~ spl6_97 ),
    inference(subsumption_resolution,[],[f1639,f341])).

fof(f1639,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_97 ),
    inference(resolution,[],[f1630,f81])).

fof(f1630,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_97 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1629,plain,
    ( spl6_97
  <=> ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_97])])).

fof(f1631,plain,
    ( ~ spl6_97
    | ~ spl6_2
    | ~ spl6_4
    | spl6_63 ),
    inference(avatar_split_clause,[],[f1196,f787,f99,f96,f1629])).

fof(f787,plain,
    ( spl6_63
  <=> ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f1196,plain,
    ( ~ m1_subset_1(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f1195,f97])).

fof(f1195,plain,
    ( ~ m1_subset_1(sK4(sK0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f788,f100])).

fof(f788,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f787])).

fof(f1564,plain,
    ( ~ spl6_95
    | ~ spl6_2
    | ~ spl6_4
    | spl6_39 ),
    inference(avatar_split_clause,[],[f1258,f452,f99,f96,f1562])).

fof(f1562,plain,
    ( spl6_95
  <=> ~ r1_partfun1(sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_95])])).

fof(f452,plain,
    ( spl6_39
  <=> ~ r1_partfun1(sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f1258,plain,
    ( ~ r1_partfun1(sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f1257,f97])).

fof(f1257,plain,
    ( ~ r1_partfun1(sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))))
    | ~ spl6_4
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f453,f100])).

fof(f453,plain,
    ( ~ r1_partfun1(sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f452])).

fof(f1513,plain,
    ( ~ spl6_93
    | ~ spl6_2
    | ~ spl6_4
    | spl6_41 ),
    inference(avatar_split_clause,[],[f1256,f458,f99,f96,f1511])).

fof(f1511,plain,
    ( spl6_93
  <=> ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f458,plain,
    ( spl6_41
  <=> ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1256,plain,
    ( ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f1255,f97])).

fof(f1255,plain,
    ( ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))))
    | ~ spl6_4
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f459,f100])).

fof(f459,plain,
    ( ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f458])).

fof(f1438,plain,
    ( spl6_90
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_64 ),
    inference(avatar_split_clause,[],[f1286,f790,f99,f96,f1436])).

fof(f790,plain,
    ( spl6_64
  <=> v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f1286,plain,
    ( v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f1285,f97])).

fof(f1285,plain,
    ( v1_funct_2(sK4(sK0,k1_xboole_0,sK2),sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f791,f100])).

fof(f791,plain,
    ( v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f790])).

fof(f1370,plain,
    ( ~ spl6_89
    | ~ spl6_2
    | ~ spl6_4
    | spl6_45 ),
    inference(avatar_split_clause,[],[f1252,f467,f99,f96,f1368])).

fof(f1368,plain,
    ( spl6_89
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_89])])).

fof(f467,plain,
    ( spl6_45
  <=> ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f1252,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f1251,f97])).

fof(f1251,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))))
    | ~ spl6_4
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f468,f100])).

fof(f468,plain,
    ( ~ v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f467])).

fof(f1346,plain,
    ( ~ spl6_87
    | ~ spl6_2
    | ~ spl6_4
    | spl6_61 ),
    inference(avatar_split_clause,[],[f1194,f778,f99,f96,f1344])).

fof(f778,plain,
    ( spl6_61
  <=> ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f1194,plain,
    ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f1193,f97])).

fof(f1193,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,k1_xboole_0,sK2))
    | ~ spl6_4
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f779,f100])).

fof(f779,plain,
    ( ~ r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f778])).

fof(f1336,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | spl6_59 ),
    inference(avatar_contradiction_clause,[],[f1335])).

fof(f1335,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34
    | ~ spl6_59 ),
    inference(subsumption_resolution,[],[f1334,f1192])).

fof(f1192,plain,
    ( k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) != k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f1191,f97])).

fof(f1191,plain,
    ( k1_funct_1(sK2,sK3(sK0,k1_xboole_0,sK2,sK4(sK0,k1_xboole_0,sK2))) != k1_funct_1(sK4(sK0,k1_xboole_0,sK2),sK3(sK0,k1_xboole_0,sK2,sK4(sK0,k1_xboole_0,sK2)))
    | ~ spl6_4
    | ~ spl6_59 ),
    inference(forward_demodulation,[],[f703,f100])).

fof(f703,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) != k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_59 ),
    inference(avatar_component_clause,[],[f702])).

fof(f702,plain,
    ( spl6_59
  <=> k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) != k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f1293,plain,
    ( ~ spl6_85
    | ~ spl6_2
    | ~ spl6_4
    | spl6_47 ),
    inference(avatar_split_clause,[],[f1250,f495,f99,f96,f1291])).

fof(f1291,plain,
    ( spl6_85
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f495,plain,
    ( spl6_47
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f1250,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_47 ),
    inference(forward_demodulation,[],[f1249,f97])).

fof(f1249,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_47 ),
    inference(forward_demodulation,[],[f496,f100])).

fof(f496,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f495])).

fof(f1177,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_34
    | spl6_59
    | spl6_65 ),
    inference(avatar_contradiction_clause,[],[f1176])).

fof(f1176,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_59
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1175,f1019])).

fof(f1019,plain,
    ( k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) != k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_59
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f97,f992])).

fof(f992,plain,
    ( k1_funct_1(sK2,sK3(sK0,k1_xboole_0,sK2,sK4(sK0,k1_xboole_0,sK2))) != k1_funct_1(sK4(sK0,k1_xboole_0,sK2),sK3(sK0,k1_xboole_0,sK2,sK4(sK0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_59
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f703,f941])).

fof(f941,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f849,f90])).

fof(f849,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f848,f110])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f848,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_65 ),
    inference(resolution,[],[f794,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK4(X0,X1,X2),X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1175,plain,
    ( k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1166,f90])).

fof(f1166,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_65 ),
    inference(resolution,[],[f1157,f341])).

fof(f1157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_34
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1156,f341])).

fof(f1156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1155,f90])).

fof(f1155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(duplicate_literal_removal,[],[f1150])).

fof(f1150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | k1_funct_1(sK2,sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK3(k1_xboole_0,k1_xboole_0,sK2,sK4(k1_xboole_0,k1_xboole_0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(resolution,[],[f1092,f388])).

fof(f1092,plain,
    ( ! [X13] :
        ( ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X13) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1091,f82])).

fof(f1091,plain,
    ( ! [X13] :
        ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,X13),k1_xboole_0,k1_xboole_0)
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X13) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1086,f83])).

fof(f1086,plain,
    ( ! [X13] :
        ( ~ v1_funct_2(sK4(k1_xboole_0,k1_xboole_0,X13),k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ r1_partfun1(sK2,sK4(k1_xboole_0,k1_xboole_0,X13))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X13) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(resolution,[],[f1022,f81])).

fof(f1022,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X3,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f1010,f97])).

fof(f1010,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X3,sK0,k1_xboole_0)
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f97,f965])).

fof(f965,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,sK0,k1_xboole_0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f942,f941])).

fof(f942,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
        | ~ v1_funct_2(X3,sK0,sK1)
        | ~ v1_funct_1(X3)
        | ~ r1_partfun1(sK2,X3) )
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f941,f48])).

fof(f1164,plain,
    ( spl6_82
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_56
    | spl6_65 ),
    inference(avatar_split_clause,[],[f1009,f793,f662,f109,f96,f89,f1162])).

fof(f1162,plain,
    ( spl6_82
  <=> k1_funct_1(sK2,sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f662,plain,
    ( spl6_56
  <=> k1_funct_1(sK2,sK5(k1_relset_1(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK5(k1_relset_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f1009,plain,
    ( k1_funct_1(sK2,sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))) = k1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2),sK5(k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_56
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f97,f958])).

fof(f958,plain,
    ( k1_funct_1(sK2,sK5(k1_relset_1(sK0,k1_xboole_0,sK2))) = k1_funct_1(sK4(sK0,k1_xboole_0,sK2),sK5(k1_relset_1(sK0,k1_xboole_0,sK2)))
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_56
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f941,f663])).

fof(f663,plain,
    ( k1_funct_1(sK2,sK5(k1_relset_1(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK5(k1_relset_1(sK0,sK1,sK2)))
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f662])).

fof(f1149,plain,
    ( ~ spl6_81
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_55
    | spl6_65 ),
    inference(avatar_split_clause,[],[f1008,f793,f601,f109,f96,f89,f1147])).

fof(f1147,plain,
    ( spl6_81
  <=> ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_81])])).

fof(f601,plain,
    ( spl6_55
  <=> ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f1008,plain,
    ( ~ v1_xboole_0(k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_55
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f97,f957])).

fof(f957,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_55
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f941,f602])).

fof(f602,plain,
    ( ~ v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f601])).

fof(f1142,plain,
    ( ~ spl6_79
    | ~ spl6_2
    | ~ spl6_4
    | spl6_31 ),
    inference(avatar_split_clause,[],[f328,f249,f99,f96,f1140])).

fof(f1140,plain,
    ( spl6_79
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f249,plain,
    ( spl6_31
  <=> ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f328,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))),k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f97,f313])).

fof(f313,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))),sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f100,f250])).

fof(f250,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f249])).

fof(f1135,plain,
    ( ~ spl6_77
    | ~ spl6_2
    | ~ spl6_4
    | spl6_27 ),
    inference(avatar_split_clause,[],[f326,f237,f99,f96,f1133])).

fof(f1133,plain,
    ( spl6_77
  <=> ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f237,plain,
    ( spl6_27
  <=> ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f326,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f97,f311])).

fof(f311,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))
    | ~ spl6_4
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f100,f238])).

fof(f238,plain,
    ( ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f237])).

fof(f1128,plain,
    ( ~ spl6_75
    | ~ spl6_2
    | ~ spl6_4
    | spl6_29 ),
    inference(avatar_split_clause,[],[f327,f243,f99,f96,f1126])).

fof(f1126,plain,
    ( spl6_75
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f243,plain,
    ( spl6_29
  <=> ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f327,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f97,f312])).

fof(f312,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))))
    | ~ spl6_4
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f100,f244])).

fof(f244,plain,
    ( ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f243])).

fof(f1121,plain,
    ( spl6_72
    | ~ spl6_0
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f1072,f340,f89,f1119])).

fof(f1119,plain,
    ( spl6_72
  <=> v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f1072,plain,
    ( v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1047,f90])).

fof(f1047,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_34 ),
    inference(resolution,[],[f341,f177])).

fof(f1114,plain,
    ( spl6_70
    | ~ spl6_0
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f1069,f340,f89,f1112])).

fof(f1069,plain,
    ( v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1046,f90])).

fof(f1046,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_34 ),
    inference(resolution,[],[f341,f83])).

fof(f1107,plain,
    ( ~ spl6_69
    | ~ spl6_2
    | ~ spl6_4
    | spl6_23 ),
    inference(avatar_split_clause,[],[f325,f227,f99,f96,f1105])).

fof(f1105,plain,
    ( spl6_69
  <=> ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f227,plain,
    ( spl6_23
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f325,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f97,f310])).

fof(f310,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(backward_demodulation,[],[f100,f228])).

fof(f228,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f1100,plain,
    ( ~ spl6_67
    | ~ spl6_2
    | ~ spl6_4
    | spl6_13 ),
    inference(avatar_split_clause,[],[f322,f132,f99,f96,f1098])).

fof(f1098,plain,
    ( spl6_67
  <=> ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_67])])).

fof(f132,plain,
    ( spl6_13
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f322,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f97,f306])).

fof(f306,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f100,f133])).

fof(f133,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f132])).

fof(f1093,plain,
    ( spl6_4
    | ~ spl6_0
    | ~ spl6_6
    | spl6_65 ),
    inference(avatar_split_clause,[],[f941,f793,f109,f89,f99])).

fof(f1074,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | spl6_33
    | ~ spl6_34 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_33
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f1072,f329])).

fof(f329,plain,
    ( ~ v1_relat_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f97,f314])).

fof(f314,plain,
    ( ~ v1_relat_1(sK4(sK0,k1_xboole_0,sK2))
    | ~ spl6_4
    | ~ spl6_33 ),
    inference(backward_demodulation,[],[f100,f296])).

fof(f296,plain,
    ( ~ v1_relat_1(sK4(sK0,sK1,sK2))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl6_33
  <=> ~ v1_relat_1(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f1071,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | spl6_21
    | ~ spl6_34
    | spl6_65 ),
    inference(avatar_contradiction_clause,[],[f1070])).

fof(f1070,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_34
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f1069,f1021])).

fof(f1021,plain,
    ( ~ v1_funct_1(sK4(k1_xboole_0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_65 ),
    inference(backward_demodulation,[],[f97,f994])).

fof(f994,plain,
    ( ~ v1_funct_1(sK4(sK0,k1_xboole_0,sK2))
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_21
    | ~ spl6_65 ),
    inference(forward_demodulation,[],[f199,f941])).

fof(f199,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl6_21
  <=> ~ v1_funct_1(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f933,plain,
    ( ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_60 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f931,f90])).

fof(f931,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_6
    | ~ spl6_36
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f929,f110])).

fof(f929,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_36
    | ~ spl6_60 ),
    inference(resolution,[],[f782,f354])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(sK2,sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl6_36
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f882,plain,
    ( ~ spl6_0
    | spl6_5
    | ~ spl6_6
    | spl6_63 ),
    inference(avatar_contradiction_clause,[],[f881])).

fof(f881,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f880,f90])).

fof(f880,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f879,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_5
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f879,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_6
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f878,f110])).

fof(f878,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | ~ spl6_63 ),
    inference(resolution,[],[f788,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f852,plain,
    ( ~ spl6_0
    | spl6_5
    | ~ spl6_6
    | spl6_65 ),
    inference(avatar_contradiction_clause,[],[f851])).

fof(f851,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f850,f90])).

fof(f850,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_65 ),
    inference(subsumption_resolution,[],[f849,f103])).

fof(f795,plain,
    ( spl6_60
    | ~ spl6_63
    | ~ spl6_65
    | ~ spl6_0
    | spl6_5
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f766,f705,f201,f109,f102,f89,f793,f787,f781])).

fof(f201,plain,
    ( spl6_20
  <=> v1_funct_1(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f705,plain,
    ( spl6_58
  <=> k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f766,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f765,f90])).

fof(f765,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f764,f103])).

fof(f764,plain,
    ( ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_6
    | ~ spl6_20
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f763,f202])).

fof(f202,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f763,plain,
    ( ~ v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_6
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f762,f110])).

fof(f762,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_58 ),
    inference(trivial_inequality_removal,[],[f761])).

fof(f761,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) != k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ v1_funct_2(sK4(sK0,sK1,sK2),sK0,sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK2,sK4(sK0,sK1,sK2))
    | ~ spl6_58 ),
    inference(superposition,[],[f54,f706])).

fof(f706,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f705])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,sK3(X0,X1,X2,X3)) != k1_funct_1(X3,sK3(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f707,plain,
    ( spl6_58
    | ~ spl6_0
    | spl6_5
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f692,f353,f109,f102,f89,f705])).

fof(f692,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2)))
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f687,f90])).

fof(f687,plain,
    ( k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,sK2)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(resolution,[],[f639,f110])).

fof(f639,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f638,f110])).

fof(f638,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f637,f90])).

fof(f637,plain,
    ( ! [X4] :
        ( ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_5
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f632,f103])).

fof(f632,plain,
    ( ! [X4] :
        ( k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_36 ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,
    ( ! [X4] :
        ( k1_xboole_0 = sK1
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4))) = k1_funct_1(sK4(sK0,sK1,sK2),sK3(sK0,sK1,sK2,sK4(sK0,sK1,X4)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X4) )
    | ~ spl6_36 ),
    inference(resolution,[],[f401,f354])).

fof(f401,plain,(
    ! [X12,X10,X11,X9] :
      ( r1_partfun1(X12,sK4(X9,X10,X11))
      | k1_xboole_0 = X10
      | ~ v1_funct_1(X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_funct_1(X12,sK3(X9,X10,X12,sK4(X9,X10,X11))) = k1_funct_1(sK4(X9,X10,X12),sK3(X9,X10,X12,sK4(X9,X10,X11)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11) ) ),
    inference(subsumption_resolution,[],[f400,f66])).

fof(f400,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ v1_funct_2(sK4(X9,X10,X11),X9,X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_xboole_0 = X10
      | ~ v1_funct_1(X12)
      | r1_partfun1(X12,sK4(X9,X10,X11))
      | k1_funct_1(X12,sK3(X9,X10,X12,sK4(X9,X10,X11))) = k1_funct_1(sK4(X9,X10,X12),sK3(X9,X10,X12,sK4(X9,X10,X11)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11) ) ),
    inference(subsumption_resolution,[],[f399,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k1_xboole_0 = X1
      | v1_funct_1(sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f399,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ v1_funct_1(sK4(X9,X10,X11))
      | ~ v1_funct_2(sK4(X9,X10,X11),X9,X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_xboole_0 = X10
      | ~ v1_funct_1(X12)
      | r1_partfun1(X12,sK4(X9,X10,X11))
      | k1_funct_1(X12,sK3(X9,X10,X12,sK4(X9,X10,X11))) = k1_funct_1(sK4(X9,X10,X12),sK3(X9,X10,X12,sK4(X9,X10,X11)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X11) ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ v1_funct_1(sK4(X9,X10,X11))
      | ~ v1_funct_2(sK4(X9,X10,X11),X9,X10)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_xboole_0 = X10
      | ~ v1_funct_1(X12)
      | r1_partfun1(X12,sK4(X9,X10,X11))
      | k1_funct_1(X12,sK3(X9,X10,X12,sK4(X9,X10,X11))) = k1_funct_1(sK4(X9,X10,X12),sK3(X9,X10,X12,sK4(X9,X10,X11)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | k1_xboole_0 = X10
      | ~ v1_funct_1(X11) ) ),
    inference(resolution,[],[f207,f67])).

fof(f207,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,X4,X5)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X5
      | ~ v1_funct_1(X3)
      | r1_partfun1(X3,X6)
      | k1_funct_1(X3,sK3(X4,X5,X3,X6)) = k1_funct_1(sK4(X4,X5,X3),sK3(X4,X5,X3,X6)) ) ),
    inference(duplicate_literal_removal,[],[f205])).

fof(f205,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X5
      | ~ v1_funct_1(X3)
      | r1_partfun1(X3,X6)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | k1_xboole_0 = X5
      | ~ v1_funct_1(X3)
      | k1_funct_1(X3,sK3(X4,X5,X3,X6)) = k1_funct_1(sK4(X4,X5,X3),sK3(X4,X5,X3,X6)) ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X4) = k1_funct_1(sK4(X0,X1,X2),X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ v1_funct_1(X2)
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f676,plain,
    ( spl6_49
    | ~ spl6_54 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | ~ spl6_49
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f673,f508])).

fof(f508,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl6_49
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f673,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_54 ),
    inference(backward_demodulation,[],[f666,f605])).

fof(f605,plain,
    ( v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f604])).

fof(f604,plain,
    ( spl6_54
  <=> v1_xboole_0(k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f666,plain,
    ( k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_54 ),
    inference(resolution,[],[f605,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t6_boole)).

fof(f664,plain,
    ( spl6_54
    | spl6_56
    | ~ spl6_0
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f590,f109,f102,f89,f662,f604])).

fof(f590,plain,
    ( k1_funct_1(sK2,sK5(k1_relset_1(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK5(k1_relset_1(sK0,sK1,sK2)))
    | v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f589,f103])).

fof(f589,plain,
    ( k1_funct_1(sK2,sK5(k1_relset_1(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK5(k1_relset_1(sK0,sK1,sK2)))
    | v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f582,f90])).

fof(f582,plain,
    ( ~ v1_funct_1(sK2)
    | k1_funct_1(sK2,sK5(k1_relset_1(sK0,sK1,sK2))) = k1_funct_1(sK4(sK0,sK1,sK2),sK5(k1_relset_1(sK0,sK1,sK2)))
    | v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK1
    | ~ spl6_6 ),
    inference(resolution,[],[f373,f110])).

fof(f373,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X1)
      | k1_funct_1(X1,sK5(k1_relset_1(X2,X0,X1))) = k1_funct_1(sK4(X2,X0,X1),sK5(k1_relset_1(X2,X0,X1)))
      | v1_xboole_0(k1_relset_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f191,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',existence_m1_subset_1)).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_relset_1(X1,X2,X0))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,X3) = k1_funct_1(sK4(X1,X2,X0),X3)
      | v1_xboole_0(k1_relset_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f60,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t2_subset)).

fof(f606,plain,
    ( ~ spl6_53
    | spl6_54
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f538,f109,f604,f598])).

fof(f598,plain,
    ( spl6_53
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f538,plain,
    ( v1_xboole_0(k1_relset_1(sK0,sK1,sK2))
    | ~ v1_xboole_0(sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f477,f110])).

fof(f477,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | v1_xboole_0(k1_relset_1(X7,X8,X9))
      | ~ v1_xboole_0(X7) ) ),
    inference(resolution,[],[f263,f77])).

fof(f263,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_relset_1(X1,X2,X0))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k1_relset_1(X1,X2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f159,f75])).

fof(f159,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(X13,k1_relset_1(X11,X12,X10))
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_xboole_0(X11) ) ),
    inference(resolution,[],[f73,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t5_subset)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',dt_k1_relset_1)).

fof(f512,plain,
    ( ~ spl6_49
    | spl6_50 ),
    inference(avatar_split_clause,[],[f267,f510,f507])).

fof(f510,plain,
    ( spl6_50
  <=> ! [X5,X4,X6] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | r1_partfun1(X4,X6)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,k1_xboole_0,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f267,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k1_xboole_0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X6) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k1_xboole_0,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X5)))
      | ~ v1_funct_1(X4)
      | r1_partfun1(X4,X6) ) ),
    inference(resolution,[],[f159,f79])).

fof(f497,plain,
    ( ~ spl6_47
    | spl6_45 ),
    inference(avatar_split_clause,[],[f481,f467,f495])).

fof(f481,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_45 ),
    inference(resolution,[],[f468,f257])).

fof(f257,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f255,f77])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK5(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK5(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f146,f75])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK5(k1_zfmisc_1(X2)))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f71,f77])).

fof(f472,plain,
    ( ~ spl6_39
    | ~ spl6_41
    | ~ spl6_43
    | spl6_44 ),
    inference(avatar_split_clause,[],[f434,f470,f464,f458,f452])).

fof(f470,plain,
    ( spl6_44
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f434,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))
    | ~ v1_funct_2(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),sK0,sK1)
    | ~ v1_funct_1(sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))))
    | ~ r1_partfun1(sK2,sK5(sK5(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))))) ),
    inference(resolution,[],[f402,f48])).

fof(f402,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK5(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK5(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f256,f77])).

fof(f256,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK5(k1_zfmisc_1(X1)))
      | v1_xboole_0(sK5(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f148,f75])).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,sK5(k1_zfmisc_1(X2)))
      | m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f72,f77])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',t4_subset)).

fof(f356,plain,
    ( spl6_32
    | spl6_4
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f301,f109,f89,f99,f298])).

fof(f298,plain,
    ( spl6_32
  <=> v1_relat_1(sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f301,plain,
    ( k1_xboole_0 = sK1
    | v1_relat_1(sK4(sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f286,f90])).

fof(f286,plain,
    ( k1_xboole_0 = sK1
    | ~ v1_funct_1(sK2)
    | v1_relat_1(sK4(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(resolution,[],[f183,f110])).

fof(f183,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | k1_xboole_0 = X6
      | ~ v1_funct_1(X4)
      | v1_relat_1(sK4(X5,X6,X4)) ) ),
    inference(resolution,[],[f67,f74])).

fof(f355,plain,
    ( spl6_4
    | spl6_36 ),
    inference(avatar_split_clause,[],[f303,f353,f99])).

fof(f303,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | ~ v1_funct_1(X0)
      | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f302,f66])).

fof(f302,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK4(sK0,sK1,X0),sK0,sK1)
      | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f181,f65])).

fof(f181,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | k1_xboole_0 = sK1
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(sK4(sK0,sK1,X0),sK0,sK1)
      | ~ v1_funct_1(sK4(sK0,sK1,X0))
      | ~ r1_partfun1(sK2,sK4(sK0,sK1,X0)) ) ),
    inference(resolution,[],[f67,f48])).

fof(f342,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f321,f109,f99,f96,f340])).

fof(f321,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f97,f305])).

fof(f305,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f100,f110])).

fof(f300,plain,
    ( spl6_32
    | ~ spl6_0
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f292,f109,f102,f89,f298])).

fof(f292,plain,
    ( v1_relat_1(sK4(sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f291,f90])).

fof(f291,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(sK4(sK0,sK1,sK2))
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f286,f103])).

fof(f251,plain,
    ( ~ spl6_27
    | ~ spl6_29
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f121,f249,f243,f237])).

fof(f121,plain,
    ( ~ v1_funct_2(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))),sK0,sK1)
    | ~ v1_funct_1(sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))
    | ~ r1_partfun1(sK2,sK5(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ),
    inference(resolution,[],[f77,f48])).

fof(f232,plain,
    ( ~ spl6_23
    | spl6_24
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f145,f109,f230,f227])).

fof(f230,plain,
    ( spl6_24
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl6_6 ),
    inference(resolution,[],[f71,f110])).

fof(f203,plain,
    ( spl6_20
    | ~ spl6_0
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f172,f109,f102,f89,f201])).

fof(f172,plain,
    ( v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f171,f103])).

fof(f171,plain,
    ( k1_xboole_0 = sK1
    | v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f168,f90])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK1
    | v1_funct_1(sK4(sK0,sK1,sK2))
    | ~ spl6_6 ),
    inference(resolution,[],[f65,f110])).

fof(f165,plain,
    ( ~ spl6_0
    | spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f163,f90])).

fof(f163,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f162,f143])).

fof(f143,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f162,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl6_11
    | ~ spl6_18 ),
    inference(resolution,[],[f127,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( r1_partfun1(X0,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_18
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | r1_partfun1(X0,X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f127,plain,
    ( ~ r1_partfun1(sK2,sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_11
  <=> ~ r1_partfun1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f155,plain,
    ( spl6_16
    | spl6_18 ),
    inference(avatar_split_clause,[],[f59,f153,f150])).

fof(f150,plain,
    ( spl6_16
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_partfun1(X0,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X0,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => r1_partfun1(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',reflexivity_r1_partfun1)).

fof(f144,plain,
    ( spl6_14
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f135,f109,f142])).

fof(f135,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f74,f110])).

fof(f134,plain,
    ( ~ spl6_11
    | ~ spl6_13
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f120,f109,f89,f132,f126])).

fof(f120,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ r1_partfun1(sK2,sK2)
    | ~ spl6_0
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f119,f90])).

fof(f119,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r1_partfun1(sK2,sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f48,f110])).

fof(f118,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f70,f116])).

fof(f116,plain,
    ( spl6_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f70,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t148_funct_2.p',d2_xboole_0)).

fof(f111,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f104,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f49,f102,f96])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f50,f89])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
