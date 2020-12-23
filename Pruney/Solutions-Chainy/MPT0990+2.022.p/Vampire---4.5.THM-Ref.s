%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:32 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 327 expanded)
%              Number of leaves         :   41 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  501 (1469 expanded)
%              Number of equality atoms :   89 ( 398 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1918,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f115,f165,f317,f319,f321,f371,f387,f395,f461,f465,f467,f470,f559,f715,f810,f968,f972,f1415,f1618,f1704,f1834,f1890,f1910])).

fof(f1910,plain,(
    ~ spl4_170 ),
    inference(avatar_contradiction_clause,[],[f1891])).

fof(f1891,plain,
    ( $false
    | ~ spl4_170 ),
    inference(subsumption_resolution,[],[f49,f1887])).

fof(f1887,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_170 ),
    inference(avatar_component_clause,[],[f1885])).

fof(f1885,plain,
    ( spl4_170
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f49,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f1890,plain,
    ( ~ spl4_17
    | ~ spl4_61
    | spl4_170
    | ~ spl4_159 ),
    inference(avatar_split_clause,[],[f1883,f1831,f1885,f803,f401])).

fof(f401,plain,
    ( spl4_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f803,plain,
    ( spl4_61
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f1831,plain,
    ( spl4_159
  <=> k2_funct_1(sK2) = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_159])])).

fof(f1883,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ v4_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_159 ),
    inference(superposition,[],[f68,f1833])).

fof(f1833,plain,
    ( k2_funct_1(sK2) = k7_relat_1(sK3,sK1)
    | ~ spl4_159 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f1834,plain,
    ( ~ spl4_15
    | ~ spl4_73
    | spl4_159
    | ~ spl4_147 ),
    inference(avatar_split_clause,[],[f1812,f1690,f1831,f924,f377])).

fof(f377,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f924,plain,
    ( spl4_73
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).

fof(f1690,plain,
    ( spl4_147
  <=> k7_relat_1(sK3,sK1) = k2_funct_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).

fof(f1812,plain,
    ( k2_funct_1(sK2) = k7_relat_1(sK3,sK1)
    | ~ v4_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2)
    | ~ spl4_147 ),
    inference(superposition,[],[f1692,f68])).

fof(f1692,plain,
    ( k7_relat_1(sK3,sK1) = k2_funct_1(k7_relat_1(sK2,sK0))
    | ~ spl4_147 ),
    inference(avatar_component_clause,[],[f1690])).

fof(f1704,plain,
    ( ~ spl4_17
    | spl4_147
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f1683,f1615,f1690,f401])).

fof(f1615,plain,
    ( spl4_134
  <=> k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f1683,plain,
    ( k7_relat_1(sK3,sK1) = k2_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_134 ),
    inference(superposition,[],[f85,f1617])).

fof(f1617,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k7_relat_1(sK2,sK0))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f1615])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f67,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f1618,plain,
    ( ~ spl4_15
    | spl4_134
    | ~ spl4_113 ),
    inference(avatar_split_clause,[],[f1600,f1404,f1615,f377])).

fof(f1404,plain,
    ( spl4_113
  <=> k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f1600,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl4_113 ),
    inference(superposition,[],[f1406,f85])).

fof(f1406,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2))
    | ~ spl4_113 ),
    inference(avatar_component_clause,[],[f1404])).

fof(f1415,plain,
    ( ~ spl4_23
    | ~ spl4_20
    | ~ spl4_72
    | ~ spl4_5
    | ~ spl4_15
    | ~ spl4_47
    | spl4_113
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f1389,f458,f1404,f693,f377,f295,f920,f450,f521])).

fof(f521,plain,
    ( spl4_23
  <=> v1_relat_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f450,plain,
    ( spl4_20
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f920,plain,
    ( spl4_72
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f295,plain,
    ( spl4_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f693,plain,
    ( spl4_47
  <=> v1_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f458,plain,
    ( spl4_22
  <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1389,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2))
    | ~ v1_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k6_partfun1(sK0))
    | ~ spl4_22 ),
    inference(superposition,[],[f460,f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(k6_partfun1(X0),X1)) = k5_relat_1(k2_funct_1(X1),k6_partfun1(X0))
      | ~ v1_funct_1(k6_partfun1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k6_partfun1(X0))
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f66,f78])).

fof(f78,plain,(
    ! [X0] : k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f54,f53,f53])).

fof(f54,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0))
          | ~ v2_funct_1(X1)
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
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

fof(f460,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f458])).

fof(f972,plain,(
    spl4_73 ),
    inference(avatar_contradiction_clause,[],[f969])).

fof(f969,plain,
    ( $false
    | spl4_73 ),
    inference(subsumption_resolution,[],[f94,f926])).

fof(f926,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_73 ),
    inference(avatar_component_clause,[],[f924])).

fof(f94,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f71,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f968,plain,(
    spl4_72 ),
    inference(avatar_contradiction_clause,[],[f965])).

fof(f965,plain,
    ( $false
    | spl4_72 ),
    inference(unit_resulting_resolution,[],[f79,f922])).

fof(f922,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f920])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f810,plain,(
    spl4_61 ),
    inference(avatar_contradiction_clause,[],[f807])).

fof(f807,plain,
    ( $false
    | spl4_61 ),
    inference(subsumption_resolution,[],[f93,f805])).

fof(f805,plain,
    ( ~ v4_relat_1(sK3,sK1)
    | spl4_61 ),
    inference(avatar_component_clause,[],[f803])).

fof(f93,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f71,f43])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f715,plain,(
    spl4_47 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | spl4_47 ),
    inference(unit_resulting_resolution,[],[f81,f695])).

fof(f695,plain,
    ( ~ v1_funct_1(k6_partfun1(sK0))
    | spl4_47 ),
    inference(avatar_component_clause,[],[f693])).

fof(f81,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f58,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f559,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | spl4_23 ),
    inference(unit_resulting_resolution,[],[f60,f523,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f523,plain,
    ( ~ v1_relat_1(k6_partfun1(sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f521])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f470,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | spl4_21 ),
    inference(unit_resulting_resolution,[],[f91,f50,f456,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f456,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl4_21
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f52])).

fof(f467,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f46,f452])).

fof(f452,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f450])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f465,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl4_17 ),
    inference(subsumption_resolution,[],[f90,f403])).

fof(f403,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_17 ),
    inference(avatar_component_clause,[],[f401])).

fof(f90,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f69,f43])).

fof(f461,plain,
    ( ~ spl4_20
    | ~ spl4_5
    | ~ spl4_21
    | ~ spl4_17
    | ~ spl4_15
    | spl4_22
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f448,f330,f109,f458,f377,f401,f454,f295,f450])).

fof(f109,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f330,plain,
    ( spl4_10
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f448,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f422,f111])).

fof(f111,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f422,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_10 ),
    inference(superposition,[],[f137,f332])).

fof(f332,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f330])).

fof(f137,plain,(
    ! [X6,X7] :
      ( k5_relat_1(k2_funct_1(X6),k5_relat_1(X6,X7)) = k5_relat_1(k6_partfun1(k2_relat_1(X6)),X7)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v2_funct_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X6,X7] :
      ( k5_relat_1(k2_funct_1(X6),k5_relat_1(X6,X7)) = k5_relat_1(k6_partfun1(k2_relat_1(X6)),X7)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(k2_funct_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v2_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f61,f83])).

fof(f83,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f395,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_1
    | spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f392,f162,f330,f105,f303,f299,f295])).

fof(f299,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f303,plain,
    ( spl4_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f105,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f162,plain,
    ( spl4_4
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f392,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4 ),
    inference(superposition,[],[f75,f164])).

fof(f164,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f387,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f91,f379])).

fof(f379,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f377])).

fof(f371,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f50,f41,f43,f52,f160,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f160,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_3
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f41,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f321,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f41,f305])).

fof(f305,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f303])).

fof(f319,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f43,f301])).

fof(f301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f299])).

fof(f317,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f50,f297])).

fof(f297,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f295])).

fof(f165,plain,
    ( ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f155,f162,f158])).

fof(f155,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f151,f45])).

fof(f45,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f151,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f74,f60])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f115,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f52,f107])).

fof(f107,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f113,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f103,f109,f105])).

fof(f103,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f44,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 17:22:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.53  % (23959)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (23965)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (23966)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (23978)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (23971)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (23957)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (23961)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (23979)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (23956)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (23976)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (23970)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (23955)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (23982)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (23985)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (23974)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (23962)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (23964)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (23984)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (23981)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (23977)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (23967)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (23968)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.57  % (23983)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (23973)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (23969)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.58  % (23963)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.58  % (23975)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.58  % (23972)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.58  % (23972)Refutation not found, incomplete strategy% (23972)------------------------------
% 1.56/0.58  % (23972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (23972)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (23972)Memory used [KB]: 10746
% 1.56/0.58  % (23972)Time elapsed: 0.157 s
% 1.56/0.58  % (23972)------------------------------
% 1.56/0.58  % (23972)------------------------------
% 1.56/0.58  % (23960)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.56/0.59  % (23980)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.01/0.69  % (23969)Refutation found. Thanks to Tanya!
% 2.01/0.69  % SZS status Theorem for theBenchmark
% 2.01/0.69  % SZS output start Proof for theBenchmark
% 2.01/0.69  fof(f1918,plain,(
% 2.01/0.69    $false),
% 2.01/0.69    inference(avatar_sat_refutation,[],[f113,f115,f165,f317,f319,f321,f371,f387,f395,f461,f465,f467,f470,f559,f715,f810,f968,f972,f1415,f1618,f1704,f1834,f1890,f1910])).
% 2.01/0.69  fof(f1910,plain,(
% 2.01/0.69    ~spl4_170),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f1891])).
% 2.01/0.69  fof(f1891,plain,(
% 2.01/0.69    $false | ~spl4_170),
% 2.01/0.69    inference(subsumption_resolution,[],[f49,f1887])).
% 2.01/0.69  fof(f1887,plain,(
% 2.01/0.69    sK3 = k2_funct_1(sK2) | ~spl4_170),
% 2.01/0.69    inference(avatar_component_clause,[],[f1885])).
% 2.01/0.69  fof(f1885,plain,(
% 2.01/0.69    spl4_170 <=> sK3 = k2_funct_1(sK2)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).
% 2.01/0.69  fof(f49,plain,(
% 2.01/0.69    sK3 != k2_funct_1(sK2)),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f21,plain,(
% 2.01/0.69    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.01/0.69    inference(flattening,[],[f20])).
% 2.01/0.69  fof(f20,plain,(
% 2.01/0.69    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.01/0.69    inference(ennf_transformation,[],[f19])).
% 2.01/0.69  fof(f19,negated_conjecture,(
% 2.01/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.01/0.69    inference(negated_conjecture,[],[f18])).
% 2.01/0.69  fof(f18,conjecture,(
% 2.01/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.01/0.69  fof(f1890,plain,(
% 2.01/0.69    ~spl4_17 | ~spl4_61 | spl4_170 | ~spl4_159),
% 2.01/0.69    inference(avatar_split_clause,[],[f1883,f1831,f1885,f803,f401])).
% 2.01/0.69  fof(f401,plain,(
% 2.01/0.69    spl4_17 <=> v1_relat_1(sK3)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.01/0.69  fof(f803,plain,(
% 2.01/0.69    spl4_61 <=> v4_relat_1(sK3,sK1)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 2.01/0.69  fof(f1831,plain,(
% 2.01/0.69    spl4_159 <=> k2_funct_1(sK2) = k7_relat_1(sK3,sK1)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_159])])).
% 2.01/0.69  fof(f1883,plain,(
% 2.01/0.69    sK3 = k2_funct_1(sK2) | ~v4_relat_1(sK3,sK1) | ~v1_relat_1(sK3) | ~spl4_159),
% 2.01/0.69    inference(superposition,[],[f68,f1833])).
% 2.01/0.69  fof(f1833,plain,(
% 2.01/0.69    k2_funct_1(sK2) = k7_relat_1(sK3,sK1) | ~spl4_159),
% 2.01/0.69    inference(avatar_component_clause,[],[f1831])).
% 2.01/0.69  fof(f68,plain,(
% 2.01/0.69    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f31])).
% 2.01/0.69  fof(f31,plain,(
% 2.01/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.01/0.69    inference(flattening,[],[f30])).
% 2.01/0.69  fof(f30,plain,(
% 2.01/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.01/0.69    inference(ennf_transformation,[],[f1])).
% 2.01/0.69  fof(f1,axiom,(
% 2.01/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 2.01/0.69  fof(f1834,plain,(
% 2.01/0.69    ~spl4_15 | ~spl4_73 | spl4_159 | ~spl4_147),
% 2.01/0.69    inference(avatar_split_clause,[],[f1812,f1690,f1831,f924,f377])).
% 2.01/0.69  fof(f377,plain,(
% 2.01/0.69    spl4_15 <=> v1_relat_1(sK2)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.01/0.69  fof(f924,plain,(
% 2.01/0.69    spl4_73 <=> v4_relat_1(sK2,sK0)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_73])])).
% 2.01/0.69  fof(f1690,plain,(
% 2.01/0.69    spl4_147 <=> k7_relat_1(sK3,sK1) = k2_funct_1(k7_relat_1(sK2,sK0))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_147])])).
% 2.01/0.69  fof(f1812,plain,(
% 2.01/0.69    k2_funct_1(sK2) = k7_relat_1(sK3,sK1) | ~v4_relat_1(sK2,sK0) | ~v1_relat_1(sK2) | ~spl4_147),
% 2.01/0.69    inference(superposition,[],[f1692,f68])).
% 2.01/0.69  fof(f1692,plain,(
% 2.01/0.69    k7_relat_1(sK3,sK1) = k2_funct_1(k7_relat_1(sK2,sK0)) | ~spl4_147),
% 2.01/0.69    inference(avatar_component_clause,[],[f1690])).
% 2.01/0.69  fof(f1704,plain,(
% 2.01/0.69    ~spl4_17 | spl4_147 | ~spl4_134),
% 2.01/0.69    inference(avatar_split_clause,[],[f1683,f1615,f1690,f401])).
% 2.01/0.69  fof(f1615,plain,(
% 2.01/0.69    spl4_134 <=> k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k7_relat_1(sK2,sK0))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 2.01/0.69  fof(f1683,plain,(
% 2.01/0.69    k7_relat_1(sK3,sK1) = k2_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK3) | ~spl4_134),
% 2.01/0.69    inference(superposition,[],[f85,f1617])).
% 2.01/0.69  fof(f1617,plain,(
% 2.01/0.69    k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k7_relat_1(sK2,sK0)) | ~spl4_134),
% 2.01/0.69    inference(avatar_component_clause,[],[f1615])).
% 2.01/0.69  fof(f85,plain,(
% 2.01/0.69    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.01/0.69    inference(definition_unfolding,[],[f67,f53])).
% 2.01/0.69  fof(f53,plain,(
% 2.01/0.69    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f17])).
% 2.01/0.69  fof(f17,axiom,(
% 2.01/0.69    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.01/0.69  fof(f67,plain,(
% 2.01/0.69    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f29])).
% 2.01/0.69  fof(f29,plain,(
% 2.01/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.01/0.69    inference(ennf_transformation,[],[f3])).
% 2.01/0.69  fof(f3,axiom,(
% 2.01/0.69    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.01/0.69  fof(f1618,plain,(
% 2.01/0.69    ~spl4_15 | spl4_134 | ~spl4_113),
% 2.01/0.69    inference(avatar_split_clause,[],[f1600,f1404,f1615,f377])).
% 2.01/0.69  fof(f1404,plain,(
% 2.01/0.69    spl4_113 <=> k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).
% 2.01/0.69  fof(f1600,plain,(
% 2.01/0.69    k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(sK2) | ~spl4_113),
% 2.01/0.69    inference(superposition,[],[f1406,f85])).
% 2.01/0.69  fof(f1406,plain,(
% 2.01/0.69    k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) | ~spl4_113),
% 2.01/0.69    inference(avatar_component_clause,[],[f1404])).
% 2.01/0.69  fof(f1415,plain,(
% 2.01/0.69    ~spl4_23 | ~spl4_20 | ~spl4_72 | ~spl4_5 | ~spl4_15 | ~spl4_47 | spl4_113 | ~spl4_22),
% 2.01/0.69    inference(avatar_split_clause,[],[f1389,f458,f1404,f693,f377,f295,f920,f450,f521])).
% 2.01/0.69  fof(f521,plain,(
% 2.01/0.69    spl4_23 <=> v1_relat_1(k6_partfun1(sK0))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.01/0.69  fof(f450,plain,(
% 2.01/0.69    spl4_20 <=> v2_funct_1(sK2)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.01/0.69  fof(f920,plain,(
% 2.01/0.69    spl4_72 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 2.01/0.69  fof(f295,plain,(
% 2.01/0.69    spl4_5 <=> v1_funct_1(sK2)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.01/0.69  fof(f693,plain,(
% 2.01/0.69    spl4_47 <=> v1_funct_1(k6_partfun1(sK0))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 2.01/0.69  fof(f458,plain,(
% 2.01/0.69    spl4_22 <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 2.01/0.69  fof(f1389,plain,(
% 2.01/0.69    k5_relat_1(k6_partfun1(sK1),sK3) = k2_funct_1(k5_relat_1(k6_partfun1(sK0),sK2)) | ~v1_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k6_partfun1(sK0)) | ~v2_funct_1(sK2) | ~v1_relat_1(k6_partfun1(sK0)) | ~spl4_22),
% 2.01/0.69    inference(superposition,[],[f460,f190])).
% 2.01/0.69  fof(f190,plain,(
% 2.01/0.69    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(k6_partfun1(X0),X1)) = k5_relat_1(k2_funct_1(X1),k6_partfun1(X0)) | ~v1_funct_1(k6_partfun1(X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k6_partfun1(X0)) | ~v2_funct_1(X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 2.01/0.69    inference(superposition,[],[f66,f78])).
% 2.01/0.69  fof(f78,plain,(
% 2.01/0.69    ( ! [X0] : (k6_partfun1(X0) = k2_funct_1(k6_partfun1(X0))) )),
% 2.01/0.69    inference(definition_unfolding,[],[f54,f53,f53])).
% 2.01/0.69  fof(f54,plain,(
% 2.01/0.69    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 2.01/0.69    inference(cnf_transformation,[],[f9])).
% 2.01/0.69  fof(f9,axiom,(
% 2.01/0.69    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 2.01/0.69  fof(f66,plain,(
% 2.01/0.69    ( ! [X0,X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v2_funct_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f28])).
% 2.01/0.69  fof(f28,plain,(
% 2.01/0.69    ! [X0] : (! [X1] : (k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.69    inference(flattening,[],[f27])).
% 2.01/0.69  fof(f27,plain,(
% 2.01/0.69    ! [X0] : (! [X1] : ((k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.69    inference(ennf_transformation,[],[f8])).
% 2.01/0.69  fof(f8,axiom,(
% 2.01/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k2_funct_1(k5_relat_1(X0,X1)) = k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)))))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).
% 2.01/0.69  fof(f460,plain,(
% 2.01/0.69    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_22),
% 2.01/0.69    inference(avatar_component_clause,[],[f458])).
% 2.01/0.69  fof(f972,plain,(
% 2.01/0.69    spl4_73),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f969])).
% 2.01/0.69  fof(f969,plain,(
% 2.01/0.69    $false | spl4_73),
% 2.01/0.69    inference(subsumption_resolution,[],[f94,f926])).
% 2.01/0.69  fof(f926,plain,(
% 2.01/0.69    ~v4_relat_1(sK2,sK0) | spl4_73),
% 2.01/0.69    inference(avatar_component_clause,[],[f924])).
% 2.01/0.69  fof(f94,plain,(
% 2.01/0.69    v4_relat_1(sK2,sK0)),
% 2.01/0.69    inference(resolution,[],[f71,f52])).
% 2.01/0.69  fof(f52,plain,(
% 2.01/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f71,plain,(
% 2.01/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f34])).
% 2.01/0.69  fof(f34,plain,(
% 2.01/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.69    inference(ennf_transformation,[],[f11])).
% 2.01/0.69  fof(f11,axiom,(
% 2.01/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.01/0.69  fof(f968,plain,(
% 2.01/0.69    spl4_72),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f965])).
% 2.01/0.69  fof(f965,plain,(
% 2.01/0.69    $false | spl4_72),
% 2.01/0.69    inference(unit_resulting_resolution,[],[f79,f922])).
% 2.01/0.69  fof(f922,plain,(
% 2.01/0.69    ~v2_funct_1(k6_partfun1(sK0)) | spl4_72),
% 2.01/0.69    inference(avatar_component_clause,[],[f920])).
% 2.01/0.69  fof(f79,plain,(
% 2.01/0.69    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.01/0.69    inference(definition_unfolding,[],[f56,f53])).
% 2.01/0.69  fof(f56,plain,(
% 2.01/0.69    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.01/0.69    inference(cnf_transformation,[],[f6])).
% 2.01/0.69  fof(f6,axiom,(
% 2.01/0.69    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.01/0.69  fof(f810,plain,(
% 2.01/0.69    spl4_61),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f807])).
% 2.01/0.69  fof(f807,plain,(
% 2.01/0.69    $false | spl4_61),
% 2.01/0.69    inference(subsumption_resolution,[],[f93,f805])).
% 2.01/0.69  fof(f805,plain,(
% 2.01/0.69    ~v4_relat_1(sK3,sK1) | spl4_61),
% 2.01/0.69    inference(avatar_component_clause,[],[f803])).
% 2.01/0.69  fof(f93,plain,(
% 2.01/0.69    v4_relat_1(sK3,sK1)),
% 2.01/0.69    inference(resolution,[],[f71,f43])).
% 2.01/0.69  fof(f43,plain,(
% 2.01/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f715,plain,(
% 2.01/0.69    spl4_47),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f712])).
% 2.01/0.69  fof(f712,plain,(
% 2.01/0.69    $false | spl4_47),
% 2.01/0.69    inference(unit_resulting_resolution,[],[f81,f695])).
% 2.01/0.69  fof(f695,plain,(
% 2.01/0.69    ~v1_funct_1(k6_partfun1(sK0)) | spl4_47),
% 2.01/0.69    inference(avatar_component_clause,[],[f693])).
% 2.01/0.69  fof(f81,plain,(
% 2.01/0.69    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 2.01/0.69    inference(definition_unfolding,[],[f58,f53])).
% 2.01/0.69  fof(f58,plain,(
% 2.01/0.69    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 2.01/0.69    inference(cnf_transformation,[],[f5])).
% 2.01/0.69  fof(f5,axiom,(
% 2.01/0.69    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 2.01/0.69  fof(f559,plain,(
% 2.01/0.69    spl4_23),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f555])).
% 2.01/0.69  fof(f555,plain,(
% 2.01/0.69    $false | spl4_23),
% 2.01/0.69    inference(unit_resulting_resolution,[],[f60,f523,f69])).
% 2.01/0.69  fof(f69,plain,(
% 2.01/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f32])).
% 2.01/0.69  fof(f32,plain,(
% 2.01/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.69    inference(ennf_transformation,[],[f10])).
% 2.01/0.69  fof(f10,axiom,(
% 2.01/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.01/0.69  fof(f523,plain,(
% 2.01/0.69    ~v1_relat_1(k6_partfun1(sK0)) | spl4_23),
% 2.01/0.69    inference(avatar_component_clause,[],[f521])).
% 2.01/0.69  fof(f60,plain,(
% 2.01/0.69    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.01/0.69    inference(cnf_transformation,[],[f15])).
% 2.01/0.69  fof(f15,axiom,(
% 2.01/0.69    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.01/0.69  fof(f470,plain,(
% 2.01/0.69    spl4_21),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f468])).
% 2.01/0.69  fof(f468,plain,(
% 2.01/0.69    $false | spl4_21),
% 2.01/0.69    inference(unit_resulting_resolution,[],[f91,f50,f456,f62])).
% 2.01/0.69  fof(f62,plain,(
% 2.01/0.69    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f24])).
% 2.01/0.69  fof(f24,plain,(
% 2.01/0.69    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.69    inference(flattening,[],[f23])).
% 2.01/0.69  fof(f23,plain,(
% 2.01/0.69    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.69    inference(ennf_transformation,[],[f4])).
% 2.01/0.69  fof(f4,axiom,(
% 2.01/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.01/0.69  fof(f456,plain,(
% 2.01/0.69    ~v1_relat_1(k2_funct_1(sK2)) | spl4_21),
% 2.01/0.69    inference(avatar_component_clause,[],[f454])).
% 2.01/0.69  fof(f454,plain,(
% 2.01/0.69    spl4_21 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 2.01/0.69  fof(f50,plain,(
% 2.01/0.69    v1_funct_1(sK2)),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f91,plain,(
% 2.01/0.69    v1_relat_1(sK2)),
% 2.01/0.69    inference(resolution,[],[f69,f52])).
% 2.01/0.69  fof(f467,plain,(
% 2.01/0.69    spl4_20),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f466])).
% 2.01/0.69  fof(f466,plain,(
% 2.01/0.69    $false | spl4_20),
% 2.01/0.69    inference(subsumption_resolution,[],[f46,f452])).
% 2.01/0.69  fof(f452,plain,(
% 2.01/0.69    ~v2_funct_1(sK2) | spl4_20),
% 2.01/0.69    inference(avatar_component_clause,[],[f450])).
% 2.01/0.69  fof(f46,plain,(
% 2.01/0.69    v2_funct_1(sK2)),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f465,plain,(
% 2.01/0.69    spl4_17),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f462])).
% 2.01/0.69  fof(f462,plain,(
% 2.01/0.69    $false | spl4_17),
% 2.01/0.69    inference(subsumption_resolution,[],[f90,f403])).
% 2.01/0.69  fof(f403,plain,(
% 2.01/0.69    ~v1_relat_1(sK3) | spl4_17),
% 2.01/0.69    inference(avatar_component_clause,[],[f401])).
% 2.01/0.69  fof(f90,plain,(
% 2.01/0.69    v1_relat_1(sK3)),
% 2.01/0.69    inference(resolution,[],[f69,f43])).
% 2.01/0.69  fof(f461,plain,(
% 2.01/0.69    ~spl4_20 | ~spl4_5 | ~spl4_21 | ~spl4_17 | ~spl4_15 | spl4_22 | ~spl4_2 | ~spl4_10),
% 2.01/0.69    inference(avatar_split_clause,[],[f448,f330,f109,f458,f377,f401,f454,f295,f450])).
% 2.01/0.69  fof(f109,plain,(
% 2.01/0.69    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.01/0.69  fof(f330,plain,(
% 2.01/0.69    spl4_10 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.01/0.69  fof(f448,plain,(
% 2.01/0.69    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_2 | ~spl4_10)),
% 2.01/0.69    inference(forward_demodulation,[],[f422,f111])).
% 2.01/0.69  fof(f111,plain,(
% 2.01/0.69    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 2.01/0.69    inference(avatar_component_clause,[],[f109])).
% 2.01/0.69  fof(f422,plain,(
% 2.01/0.69    k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_10),
% 2.01/0.69    inference(superposition,[],[f137,f332])).
% 2.01/0.69  fof(f332,plain,(
% 2.01/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_10),
% 2.01/0.69    inference(avatar_component_clause,[],[f330])).
% 2.01/0.69  fof(f137,plain,(
% 2.01/0.69    ( ! [X6,X7] : (k5_relat_1(k2_funct_1(X6),k5_relat_1(X6,X7)) = k5_relat_1(k6_partfun1(k2_relat_1(X6)),X7) | ~v1_relat_1(X6) | ~v1_relat_1(X7) | ~v1_relat_1(k2_funct_1(X6)) | ~v1_funct_1(X6) | ~v2_funct_1(X6)) )),
% 2.01/0.69    inference(duplicate_literal_removal,[],[f132])).
% 2.01/0.69  fof(f132,plain,(
% 2.01/0.69    ( ! [X6,X7] : (k5_relat_1(k2_funct_1(X6),k5_relat_1(X6,X7)) = k5_relat_1(k6_partfun1(k2_relat_1(X6)),X7) | ~v1_relat_1(X6) | ~v1_relat_1(X7) | ~v1_relat_1(k2_funct_1(X6)) | ~v1_funct_1(X6) | ~v2_funct_1(X6) | ~v1_relat_1(X6)) )),
% 2.01/0.69    inference(superposition,[],[f61,f83])).
% 2.01/0.69  fof(f83,plain,(
% 2.01/0.69    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.69    inference(definition_unfolding,[],[f65,f53])).
% 2.01/0.69  fof(f65,plain,(
% 2.01/0.69    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 2.01/0.69    inference(cnf_transformation,[],[f26])).
% 2.01/0.69  fof(f26,plain,(
% 2.01/0.69    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.69    inference(flattening,[],[f25])).
% 2.01/0.69  fof(f25,plain,(
% 2.01/0.69    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.69    inference(ennf_transformation,[],[f7])).
% 2.01/0.69  fof(f7,axiom,(
% 2.01/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 2.01/0.69  fof(f61,plain,(
% 2.01/0.69    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f22])).
% 2.01/0.69  fof(f22,plain,(
% 2.01/0.69    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.01/0.69    inference(ennf_transformation,[],[f2])).
% 2.01/0.69  fof(f2,axiom,(
% 2.01/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.01/0.69  fof(f395,plain,(
% 2.01/0.69    ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_1 | spl4_10 | ~spl4_4),
% 2.01/0.69    inference(avatar_split_clause,[],[f392,f162,f330,f105,f303,f299,f295])).
% 2.01/0.69  fof(f299,plain,(
% 2.01/0.69    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.01/0.69  fof(f303,plain,(
% 2.01/0.69    spl4_7 <=> v1_funct_1(sK3)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.01/0.69  fof(f105,plain,(
% 2.01/0.69    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.01/0.69  fof(f162,plain,(
% 2.01/0.69    spl4_4 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.01/0.69  fof(f392,plain,(
% 2.01/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_4),
% 2.01/0.69    inference(superposition,[],[f75,f164])).
% 2.01/0.69  fof(f164,plain,(
% 2.01/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_4),
% 2.01/0.69    inference(avatar_component_clause,[],[f162])).
% 2.01/0.69  fof(f75,plain,(
% 2.01/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f38])).
% 2.01/0.69  fof(f38,plain,(
% 2.01/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.01/0.69    inference(flattening,[],[f37])).
% 2.01/0.69  fof(f37,plain,(
% 2.01/0.69    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.01/0.69    inference(ennf_transformation,[],[f16])).
% 2.01/0.69  fof(f16,axiom,(
% 2.01/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.01/0.69  fof(f387,plain,(
% 2.01/0.69    spl4_15),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f384])).
% 2.01/0.69  fof(f384,plain,(
% 2.01/0.69    $false | spl4_15),
% 2.01/0.69    inference(subsumption_resolution,[],[f91,f379])).
% 2.01/0.69  fof(f379,plain,(
% 2.01/0.69    ~v1_relat_1(sK2) | spl4_15),
% 2.01/0.69    inference(avatar_component_clause,[],[f377])).
% 2.01/0.69  fof(f371,plain,(
% 2.01/0.69    spl4_3),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f358])).
% 2.01/0.69  fof(f358,plain,(
% 2.01/0.69    $false | spl4_3),
% 2.01/0.69    inference(unit_resulting_resolution,[],[f50,f41,f43,f52,f160,f77])).
% 2.01/0.69  fof(f77,plain,(
% 2.01/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f40])).
% 2.01/0.69  fof(f40,plain,(
% 2.01/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.01/0.69    inference(flattening,[],[f39])).
% 2.01/0.69  fof(f39,plain,(
% 2.01/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.01/0.69    inference(ennf_transformation,[],[f14])).
% 2.01/0.69  fof(f14,axiom,(
% 2.01/0.69    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.01/0.69  fof(f160,plain,(
% 2.01/0.69    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_3),
% 2.01/0.69    inference(avatar_component_clause,[],[f158])).
% 2.01/0.69  fof(f158,plain,(
% 2.01/0.69    spl4_3 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.01/0.69    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.01/0.69  fof(f41,plain,(
% 2.01/0.69    v1_funct_1(sK3)),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f321,plain,(
% 2.01/0.69    spl4_7),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f320])).
% 2.01/0.69  fof(f320,plain,(
% 2.01/0.69    $false | spl4_7),
% 2.01/0.69    inference(subsumption_resolution,[],[f41,f305])).
% 2.01/0.69  fof(f305,plain,(
% 2.01/0.69    ~v1_funct_1(sK3) | spl4_7),
% 2.01/0.69    inference(avatar_component_clause,[],[f303])).
% 2.01/0.69  fof(f319,plain,(
% 2.01/0.69    spl4_6),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f318])).
% 2.01/0.69  fof(f318,plain,(
% 2.01/0.69    $false | spl4_6),
% 2.01/0.69    inference(subsumption_resolution,[],[f43,f301])).
% 2.01/0.69  fof(f301,plain,(
% 2.01/0.69    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_6),
% 2.01/0.69    inference(avatar_component_clause,[],[f299])).
% 2.01/0.69  fof(f317,plain,(
% 2.01/0.69    spl4_5),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f316])).
% 2.01/0.69  fof(f316,plain,(
% 2.01/0.69    $false | spl4_5),
% 2.01/0.69    inference(subsumption_resolution,[],[f50,f297])).
% 2.01/0.69  fof(f297,plain,(
% 2.01/0.69    ~v1_funct_1(sK2) | spl4_5),
% 2.01/0.69    inference(avatar_component_clause,[],[f295])).
% 2.01/0.69  fof(f165,plain,(
% 2.01/0.69    ~spl4_3 | spl4_4),
% 2.01/0.69    inference(avatar_split_clause,[],[f155,f162,f158])).
% 2.01/0.69  fof(f155,plain,(
% 2.01/0.69    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.01/0.69    inference(resolution,[],[f151,f45])).
% 2.01/0.69  fof(f45,plain,(
% 2.01/0.69    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  fof(f151,plain,(
% 2.01/0.69    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.01/0.69    inference(resolution,[],[f74,f60])).
% 2.01/0.69  fof(f74,plain,(
% 2.01/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.01/0.69    inference(cnf_transformation,[],[f36])).
% 2.01/0.69  fof(f36,plain,(
% 2.01/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.69    inference(flattening,[],[f35])).
% 2.01/0.69  fof(f35,plain,(
% 2.01/0.69    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.01/0.69    inference(ennf_transformation,[],[f13])).
% 2.01/0.69  fof(f13,axiom,(
% 2.01/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.01/0.69  fof(f115,plain,(
% 2.01/0.69    spl4_1),
% 2.01/0.69    inference(avatar_contradiction_clause,[],[f114])).
% 2.01/0.69  fof(f114,plain,(
% 2.01/0.69    $false | spl4_1),
% 2.01/0.69    inference(subsumption_resolution,[],[f52,f107])).
% 2.01/0.69  fof(f107,plain,(
% 2.01/0.69    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 2.01/0.69    inference(avatar_component_clause,[],[f105])).
% 2.01/0.69  fof(f113,plain,(
% 2.01/0.69    ~spl4_1 | spl4_2),
% 2.01/0.69    inference(avatar_split_clause,[],[f103,f109,f105])).
% 2.01/0.69  fof(f103,plain,(
% 2.01/0.69    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.01/0.69    inference(superposition,[],[f44,f70])).
% 2.01/0.69  fof(f70,plain,(
% 2.01/0.69    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.69    inference(cnf_transformation,[],[f33])).
% 2.01/0.69  fof(f33,plain,(
% 2.01/0.69    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.69    inference(ennf_transformation,[],[f12])).
% 2.01/0.69  fof(f12,axiom,(
% 2.01/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.01/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.01/0.69  fof(f44,plain,(
% 2.01/0.69    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.01/0.69    inference(cnf_transformation,[],[f21])).
% 2.01/0.69  % SZS output end Proof for theBenchmark
% 2.01/0.69  % (23969)------------------------------
% 2.01/0.69  % (23969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.69  % (23969)Termination reason: Refutation
% 2.01/0.69  
% 2.01/0.69  % (23969)Memory used [KB]: 8059
% 2.01/0.69  % (23969)Time elapsed: 0.253 s
% 2.01/0.69  % (23969)------------------------------
% 2.01/0.69  % (23969)------------------------------
% 2.01/0.71  % (23952)Success in time 0.336 s
%------------------------------------------------------------------------------
