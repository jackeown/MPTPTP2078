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
% DateTime   : Thu Dec  3 13:03:19 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 568 expanded)
%              Number of leaves         :   39 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  671 (2893 expanded)
%              Number of equality atoms :  102 ( 560 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f133,f484,f796,f1333,f1466,f1474,f1920,f2052,f2055,f2064,f2162,f2169,f2171,f2178,f2180,f2183,f2185])).

fof(f2185,plain,
    ( spl8_9
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f1759,f175,f179])).

fof(f179,plain,
    ( spl8_9
  <=> sK4 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f175,plain,
    ( spl8_8
  <=> r1_tarski(sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1759,plain,
    ( sK4 = sK6
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f1756,f65])).

fof(f65,plain,(
    r1_tarski(sK6,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
      | ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
      | ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) )
    & ( k1_xboole_0 = sK4
      | k1_xboole_0 != sK5 )
    & r1_tarski(sK6,sK4)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f22,f48])).

fof(f48,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
          | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
          | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
        | ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
        | ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) )
      & ( k1_xboole_0 = sK4
        | k1_xboole_0 != sK5 )
      & r1_tarski(sK6,sK4)
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | ~ v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
        | ~ v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X2,X0)
         => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
              & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
              & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X2,X0)
       => ( ( m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
            & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1)
            & v1_funct_1(k2_partfun1(X0,X1,X3,X2)) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

fof(f1756,plain,
    ( sK4 = sK6
    | ~ r1_tarski(sK6,sK4)
    | ~ spl8_8 ),
    inference(resolution,[],[f176,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f176,plain,
    ( r1_tarski(sK4,sK6)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f2183,plain,
    ( spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f1830,f184,f188])).

fof(f188,plain,
    ( spl8_11
  <=> sK7 = k2_zfmisc_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f184,plain,
    ( spl8_10
  <=> r1_tarski(k2_zfmisc_1(sK4,sK5),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f1830,plain,
    ( sK7 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f1828,f142])).

fof(f142,plain,(
    r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f86,f64])).

fof(f64,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1828,plain,
    ( sK7 = k2_zfmisc_1(sK4,sK5)
    | ~ r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))
    | ~ spl8_10 ),
    inference(resolution,[],[f185,f85])).

fof(f185,plain,
    ( r1_tarski(k2_zfmisc_1(sK4,sK5),sK7)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f2180,plain,
    ( ~ spl8_13
    | spl8_25 ),
    inference(avatar_split_clause,[],[f744,f719,f315])).

fof(f315,plain,
    ( spl8_13
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f719,plain,
    ( spl8_25
  <=> r1_tarski(sK6,k1_relat_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f744,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | spl8_25 ),
    inference(resolution,[],[f743,f65])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK6,X0)
        | ~ r1_tarski(X0,k1_xboole_0) )
    | spl8_25 ),
    inference(resolution,[],[f732,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f732,plain,
    ( ~ r1_tarski(sK6,k1_xboole_0)
    | spl8_25 ),
    inference(resolution,[],[f729,f68])).

fof(f68,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f729,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK7))
        | ~ r1_tarski(sK6,X0) )
    | spl8_25 ),
    inference(resolution,[],[f721,f102])).

fof(f721,plain,
    ( ~ r1_tarski(sK6,k1_relat_1(sK7))
    | spl8_25 ),
    inference(avatar_component_clause,[],[f719])).

fof(f2178,plain,
    ( spl8_4
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f918,f759,f126])).

fof(f126,plain,
    ( spl8_4
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f759,plain,
    ( spl8_30
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f918,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_30 ),
    inference(resolution,[],[f761,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f761,plain,
    ( sP1(sK4,sK5)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f759])).

fof(f2171,plain,
    ( spl8_29
    | spl8_30 ),
    inference(avatar_split_clause,[],[f2170,f759,f755])).

fof(f755,plain,
    ( spl8_29
  <=> sK4 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f2170,plain,
    ( sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f1939,f63])).

fof(f63,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f1939,plain,
    ( ~ v1_funct_2(sK7,sK4,sK5)
    | sP1(sK4,sK5)
    | sK4 = k1_relat_1(sK7) ),
    inference(resolution,[],[f64,f449])).

fof(f449,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f447,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f37,f46,f45,f44])).

fof(f45,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f447,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP1(X3,X4)
      | ~ sP2(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f96,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f2169,plain,
    ( ~ spl8_25
    | ~ spl8_26
    | spl8_2 ),
    inference(avatar_split_clause,[],[f2168,f117,f723,f719])).

fof(f723,plain,
    ( spl8_26
  <=> sP0(sK5,k7_relat_1(sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f117,plain,
    ( spl8_2
  <=> v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2168,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | ~ r1_tarski(sK6,k1_relat_1(sK7))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f2082,f146])).

fof(f146,plain,(
    v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f144,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f144,plain,
    ( v1_relat_1(sK7)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f69,f64])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f2082,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | ~ r1_tarski(sK6,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl8_2 ),
    inference(resolution,[],[f490,f358])).

fof(f358,plain,(
    ! [X14,X12,X13] :
      ( v1_funct_2(k7_relat_1(X12,X13),X13,X14)
      | ~ sP0(X14,k7_relat_1(X12,X13))
      | ~ r1_tarski(X13,k1_relat_1(X12))
      | ~ v1_relat_1(X12) ) ),
    inference(superposition,[],[f80,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f490,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f489,f62])).

fof(f62,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f489,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5)
    | ~ v1_funct_1(sK7)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f488,f64])).

fof(f488,plain,
    ( ~ v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl8_2 ),
    inference(superposition,[],[f119,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f119,plain,
    ( ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f2162,plain,(
    spl8_31 ),
    inference(avatar_contradiction_clause,[],[f2161])).

fof(f2161,plain,
    ( $false
    | spl8_31 ),
    inference(subsumption_resolution,[],[f2158,f146])).

fof(f2158,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_31 ),
    inference(resolution,[],[f2156,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f2156,plain,
    ( ~ r1_tarski(k7_relat_1(sK7,sK6),sK7)
    | spl8_31 ),
    inference(resolution,[],[f2150,f781])).

fof(f781,plain,
    ( ~ v5_relat_1(k7_relat_1(sK7,sK6),sK5)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f779])).

fof(f779,plain,
    ( spl8_31
  <=> v5_relat_1(k7_relat_1(sK7,sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f2150,plain,(
    ! [X21] :
      ( v5_relat_1(X21,sK5)
      | ~ r1_tarski(X21,sK7) ) ),
    inference(resolution,[],[f264,f142])).

fof(f264,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X5,X3))
      | v5_relat_1(X2,X3)
      | ~ r1_tarski(X2,X4) ) ),
    inference(resolution,[],[f206,f102])).

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f93,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2064,plain,
    ( ~ spl8_31
    | ~ spl8_1
    | spl8_26
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f2063,f783,f723,f113,f779])).

fof(f113,plain,
    ( spl8_1
  <=> v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f783,plain,
    ( spl8_32
  <=> v1_relat_1(k7_relat_1(sK7,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f2063,plain,
    ( ~ v5_relat_1(k7_relat_1(sK7,sK6),sK5)
    | ~ spl8_1
    | spl8_26
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f2062,f784])).

fof(f784,plain,
    ( v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f783])).

fof(f2062,plain,
    ( ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v5_relat_1(k7_relat_1(sK7,sK6),sK5)
    | ~ spl8_1
    | spl8_26 ),
    inference(subsumption_resolution,[],[f2057,f487])).

fof(f487,plain,
    ( v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f486,f62])).

fof(f486,plain,
    ( v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f485,f64])).

fof(f485,plain,
    ( v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(superposition,[],[f114,f103])).

fof(f114,plain,
    ( v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f2057,plain,
    ( ~ v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | ~ v5_relat_1(k7_relat_1(sK7,sK6),sK5)
    | spl8_26 ),
    inference(resolution,[],[f725,f281])).

fof(f281,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f82,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sP0(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f33,f42])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f725,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | spl8_26 ),
    inference(avatar_component_clause,[],[f723])).

fof(f2055,plain,
    ( ~ spl8_26
    | spl8_2
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f976,f755,f117,f723])).

fof(f976,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | spl8_2
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f975,f65])).

fof(f975,plain,
    ( ~ r1_tarski(sK6,sK4)
    | ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | spl8_2
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f974,f757])).

fof(f757,plain,
    ( sK4 = k1_relat_1(sK7)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f755])).

fof(f974,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | ~ r1_tarski(sK6,k1_relat_1(sK7))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f973,f146])).

fof(f973,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | ~ r1_tarski(sK6,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl8_2 ),
    inference(resolution,[],[f490,f358])).

fof(f2052,plain,
    ( spl8_3
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f2051])).

fof(f2051,plain,
    ( $false
    | spl8_3
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f2050,f65])).

fof(f2050,plain,
    ( ~ r1_tarski(sK6,sK4)
    | spl8_3
    | ~ spl8_26
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f2049,f757])).

fof(f2049,plain,
    ( ~ r1_tarski(sK6,k1_relat_1(sK7))
    | spl8_3
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f2048,f146])).

fof(f2048,plain,
    ( ~ r1_tarski(sK6,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl8_3
    | ~ spl8_26 ),
    inference(subsumption_resolution,[],[f2045,f724])).

fof(f724,plain,
    ( sP0(sK5,k7_relat_1(sK7,sK6))
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f723])).

fof(f2045,plain,
    ( ~ sP0(sK5,k7_relat_1(sK7,sK6))
    | ~ r1_tarski(sK6,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl8_3 ),
    inference(resolution,[],[f2044,f357])).

fof(f357,plain,(
    ! [X10,X11,X9] :
      ( m1_subset_1(k7_relat_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ sP0(X11,k7_relat_1(X9,X10))
      | ~ r1_tarski(X10,k1_relat_1(X9))
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f81,f74])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2044,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | spl8_3 ),
    inference(subsumption_resolution,[],[f2043,f62])).

fof(f2043,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_1(sK7)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f2042,f64])).

fof(f2042,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl8_3 ),
    inference(superposition,[],[f123,f103])).

fof(f123,plain,
    ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_3
  <=> m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1920,plain,
    ( spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f1919])).

fof(f1919,plain,
    ( $false
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f1916,f146])).

fof(f1916,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(resolution,[],[f1914,f73])).

fof(f1914,plain,
    ( ~ r1_tarski(k7_relat_1(sK7,sK4),sK7)
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(resolution,[],[f1890,f87])).

fof(f1890,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7))
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f1889,f1837])).

fof(f1837,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | ~ spl8_11 ),
    inference(backward_demodulation,[],[f64,f190])).

fof(f190,plain,
    ( sK7 = k2_zfmisc_1(sK4,sK5)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f188])).

fof(f1889,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | ~ m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7))
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f1888,f190])).

fof(f1888,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f1887,f62])).

fof(f1887,plain,
    ( ~ m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(superposition,[],[f1872,f103])).

fof(f1872,plain,
    ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK4),k1_zfmisc_1(sK7))
    | spl8_3
    | ~ spl8_9
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f1871,f190])).

fof(f1871,plain,
    ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | spl8_3
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f123,f181])).

fof(f181,plain,
    ( sK4 = sK6
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f179])).

fof(f1474,plain,
    ( ~ spl8_5
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f1473])).

fof(f1473,plain,
    ( $false
    | ~ spl8_5
    | spl8_13 ),
    inference(subsumption_resolution,[],[f1432,f68])).

fof(f1432,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | spl8_13 ),
    inference(backward_demodulation,[],[f317,f132])).

fof(f132,plain,
    ( k1_xboole_0 = sK4
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f317,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f315])).

fof(f1466,plain,
    ( ~ spl8_5
    | spl8_8 ),
    inference(avatar_contradiction_clause,[],[f1465])).

fof(f1465,plain,
    ( $false
    | ~ spl8_5
    | spl8_8 ),
    inference(subsumption_resolution,[],[f1424,f68])).

fof(f1424,plain,
    ( ~ r1_tarski(k1_xboole_0,sK6)
    | ~ spl8_5
    | spl8_8 ),
    inference(backward_demodulation,[],[f177,f132])).

fof(f177,plain,
    ( ~ r1_tarski(sK4,sK6)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f175])).

fof(f1333,plain,
    ( ~ spl8_4
    | spl8_10 ),
    inference(avatar_contradiction_clause,[],[f1332])).

fof(f1332,plain,
    ( $false
    | ~ spl8_4
    | spl8_10 ),
    inference(subsumption_resolution,[],[f1331,f68])).

fof(f1331,plain,
    ( ~ r1_tarski(k1_xboole_0,sK7)
    | ~ spl8_4
    | spl8_10 ),
    inference(forward_demodulation,[],[f1302,f106])).

fof(f106,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1302,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,k1_xboole_0),sK7)
    | ~ spl8_4
    | spl8_10 ),
    inference(backward_demodulation,[],[f186,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK5
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f186,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),sK7)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f184])).

fof(f796,plain,(
    spl8_32 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | spl8_32 ),
    inference(subsumption_resolution,[],[f794,f146])).

fof(f794,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_32 ),
    inference(resolution,[],[f785,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f785,plain,
    ( ~ v1_relat_1(k7_relat_1(sK7,sK6))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f783])).

fof(f484,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f483])).

fof(f483,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f482,f146])).

fof(f482,plain,
    ( ~ v1_relat_1(sK7)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f481,f62])).

fof(f481,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | spl8_1 ),
    inference(resolution,[],[f480,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k7_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k7_relat_1(X0,X1))
        & v1_relat_1(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

fof(f480,plain,
    ( ~ v1_funct_1(k7_relat_1(sK7,sK6))
    | spl8_1 ),
    inference(subsumption_resolution,[],[f479,f62])).

fof(f479,plain,
    ( ~ v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ v1_funct_1(sK7)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f478,f64])).

fof(f478,plain,
    ( ~ v1_funct_1(k7_relat_1(sK7,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | ~ v1_funct_1(sK7)
    | spl8_1 ),
    inference(superposition,[],[f115,f103])).

fof(f115,plain,
    ( ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f133,plain,
    ( ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f66,f130,f126])).

fof(f66,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f49])).

fof(f124,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f67,f121,f117,f113])).

fof(f67,plain,
    ( ~ m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)
    | ~ v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:43:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (27664)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (27663)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (27678)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (27662)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (27683)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (27675)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (27679)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (27667)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (27680)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (27671)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (27672)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (27670)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (27666)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (27665)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (27674)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (27661)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27660)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (27682)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (27668)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (27677)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (27681)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.56  % (27684)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (27669)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (27673)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (27685)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.56  % (27676)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.01/0.63  % (27664)Refutation found. Thanks to Tanya!
% 2.01/0.63  % SZS status Theorem for theBenchmark
% 2.01/0.63  % SZS output start Proof for theBenchmark
% 2.01/0.63  fof(f2192,plain,(
% 2.01/0.63    $false),
% 2.01/0.63    inference(avatar_sat_refutation,[],[f124,f133,f484,f796,f1333,f1466,f1474,f1920,f2052,f2055,f2064,f2162,f2169,f2171,f2178,f2180,f2183,f2185])).
% 2.01/0.63  fof(f2185,plain,(
% 2.01/0.63    spl8_9 | ~spl8_8),
% 2.01/0.63    inference(avatar_split_clause,[],[f1759,f175,f179])).
% 2.01/0.63  fof(f179,plain,(
% 2.01/0.63    spl8_9 <=> sK4 = sK6),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 2.01/0.63  fof(f175,plain,(
% 2.01/0.63    spl8_8 <=> r1_tarski(sK4,sK6)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 2.01/0.63  fof(f1759,plain,(
% 2.01/0.63    sK4 = sK6 | ~spl8_8),
% 2.01/0.63    inference(subsumption_resolution,[],[f1756,f65])).
% 2.01/0.63  fof(f65,plain,(
% 2.01/0.63    r1_tarski(sK6,sK4)),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  fof(f49,plain,(
% 2.01/0.63    (~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 2.01/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f22,f48])).
% 2.01/0.63  fof(f48,plain,(
% 2.01/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))) & (k1_xboole_0 = sK4 | k1_xboole_0 != sK5) & r1_tarski(sK6,sK4) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 2.01/0.63    introduced(choice_axiom,[])).
% 2.01/0.63  fof(f22,plain,(
% 2.01/0.63    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.01/0.63    inference(flattening,[],[f21])).
% 2.01/0.63  fof(f21,plain,(
% 2.01/0.63    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.01/0.63    inference(ennf_transformation,[],[f20])).
% 2.01/0.63  fof(f20,negated_conjecture,(
% 2.01/0.63    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.01/0.63    inference(negated_conjecture,[],[f19])).
% 2.01/0.63  fof(f19,conjecture,(
% 2.01/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 2.01/0.63  fof(f1756,plain,(
% 2.01/0.63    sK4 = sK6 | ~r1_tarski(sK6,sK4) | ~spl8_8),
% 2.01/0.63    inference(resolution,[],[f176,f85])).
% 2.01/0.63  fof(f85,plain,(
% 2.01/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f53])).
% 2.01/0.63  fof(f53,plain,(
% 2.01/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.63    inference(flattening,[],[f52])).
% 2.01/0.63  fof(f52,plain,(
% 2.01/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.01/0.63    inference(nnf_transformation,[],[f1])).
% 2.01/0.63  fof(f1,axiom,(
% 2.01/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.01/0.63  fof(f176,plain,(
% 2.01/0.63    r1_tarski(sK4,sK6) | ~spl8_8),
% 2.01/0.63    inference(avatar_component_clause,[],[f175])).
% 2.01/0.63  fof(f2183,plain,(
% 2.01/0.63    spl8_11 | ~spl8_10),
% 2.01/0.63    inference(avatar_split_clause,[],[f1830,f184,f188])).
% 2.01/0.63  fof(f188,plain,(
% 2.01/0.63    spl8_11 <=> sK7 = k2_zfmisc_1(sK4,sK5)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 2.01/0.63  fof(f184,plain,(
% 2.01/0.63    spl8_10 <=> r1_tarski(k2_zfmisc_1(sK4,sK5),sK7)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 2.01/0.63  fof(f1830,plain,(
% 2.01/0.63    sK7 = k2_zfmisc_1(sK4,sK5) | ~spl8_10),
% 2.01/0.63    inference(subsumption_resolution,[],[f1828,f142])).
% 2.01/0.63  fof(f142,plain,(
% 2.01/0.63    r1_tarski(sK7,k2_zfmisc_1(sK4,sK5))),
% 2.01/0.63    inference(resolution,[],[f86,f64])).
% 2.01/0.63  fof(f64,plain,(
% 2.01/0.63    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  fof(f86,plain,(
% 2.01/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f54])).
% 2.01/0.63  fof(f54,plain,(
% 2.01/0.63    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.01/0.63    inference(nnf_transformation,[],[f6])).
% 2.01/0.63  fof(f6,axiom,(
% 2.01/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.01/0.63  fof(f1828,plain,(
% 2.01/0.63    sK7 = k2_zfmisc_1(sK4,sK5) | ~r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) | ~spl8_10),
% 2.01/0.63    inference(resolution,[],[f185,f85])).
% 2.01/0.63  fof(f185,plain,(
% 2.01/0.63    r1_tarski(k2_zfmisc_1(sK4,sK5),sK7) | ~spl8_10),
% 2.01/0.63    inference(avatar_component_clause,[],[f184])).
% 2.01/0.63  fof(f2180,plain,(
% 2.01/0.63    ~spl8_13 | spl8_25),
% 2.01/0.63    inference(avatar_split_clause,[],[f744,f719,f315])).
% 2.01/0.63  fof(f315,plain,(
% 2.01/0.63    spl8_13 <=> r1_tarski(sK4,k1_xboole_0)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 2.01/0.63  fof(f719,plain,(
% 2.01/0.63    spl8_25 <=> r1_tarski(sK6,k1_relat_1(sK7))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 2.01/0.63  fof(f744,plain,(
% 2.01/0.63    ~r1_tarski(sK4,k1_xboole_0) | spl8_25),
% 2.01/0.63    inference(resolution,[],[f743,f65])).
% 2.01/0.63  fof(f743,plain,(
% 2.01/0.63    ( ! [X0] : (~r1_tarski(sK6,X0) | ~r1_tarski(X0,k1_xboole_0)) ) | spl8_25),
% 2.01/0.63    inference(resolution,[],[f732,f102])).
% 2.01/0.63  fof(f102,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f39])).
% 2.01/0.63  fof(f39,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.01/0.63    inference(flattening,[],[f38])).
% 2.01/0.63  fof(f38,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.01/0.63    inference(ennf_transformation,[],[f2])).
% 2.01/0.63  fof(f2,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.01/0.63  fof(f732,plain,(
% 2.01/0.63    ~r1_tarski(sK6,k1_xboole_0) | spl8_25),
% 2.01/0.63    inference(resolution,[],[f729,f68])).
% 2.01/0.63  fof(f68,plain,(
% 2.01/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f3])).
% 2.01/0.63  fof(f3,axiom,(
% 2.01/0.63    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.01/0.63  fof(f729,plain,(
% 2.01/0.63    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(sK7)) | ~r1_tarski(sK6,X0)) ) | spl8_25),
% 2.01/0.63    inference(resolution,[],[f721,f102])).
% 2.01/0.63  fof(f721,plain,(
% 2.01/0.63    ~r1_tarski(sK6,k1_relat_1(sK7)) | spl8_25),
% 2.01/0.63    inference(avatar_component_clause,[],[f719])).
% 2.01/0.63  fof(f2178,plain,(
% 2.01/0.63    spl8_4 | ~spl8_30),
% 2.01/0.63    inference(avatar_split_clause,[],[f918,f759,f126])).
% 2.01/0.63  fof(f126,plain,(
% 2.01/0.63    spl8_4 <=> k1_xboole_0 = sK5),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 2.01/0.63  fof(f759,plain,(
% 2.01/0.63    spl8_30 <=> sP1(sK4,sK5)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 2.01/0.63  fof(f918,plain,(
% 2.01/0.63    k1_xboole_0 = sK5 | ~spl8_30),
% 2.01/0.63    inference(resolution,[],[f761,f98])).
% 2.01/0.63  fof(f98,plain,(
% 2.01/0.63    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 2.01/0.63    inference(cnf_transformation,[],[f61])).
% 2.01/0.63  fof(f61,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 2.01/0.63    inference(nnf_transformation,[],[f44])).
% 2.01/0.63  fof(f44,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 2.01/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.01/0.63  fof(f761,plain,(
% 2.01/0.63    sP1(sK4,sK5) | ~spl8_30),
% 2.01/0.63    inference(avatar_component_clause,[],[f759])).
% 2.01/0.63  fof(f2171,plain,(
% 2.01/0.63    spl8_29 | spl8_30),
% 2.01/0.63    inference(avatar_split_clause,[],[f2170,f759,f755])).
% 2.01/0.63  fof(f755,plain,(
% 2.01/0.63    spl8_29 <=> sK4 = k1_relat_1(sK7)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 2.01/0.63  fof(f2170,plain,(
% 2.01/0.63    sP1(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1939,f63])).
% 2.01/0.63  fof(f63,plain,(
% 2.01/0.63    v1_funct_2(sK7,sK4,sK5)),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  fof(f1939,plain,(
% 2.01/0.63    ~v1_funct_2(sK7,sK4,sK5) | sP1(sK4,sK5) | sK4 = k1_relat_1(sK7)),
% 2.01/0.63    inference(resolution,[],[f64,f449])).
% 2.01/0.63  fof(f449,plain,(
% 2.01/0.63    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | k1_relat_1(X5) = X3) )),
% 2.01/0.63    inference(subsumption_resolution,[],[f447,f100])).
% 2.01/0.63  fof(f100,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f47])).
% 2.01/0.63  fof(f47,plain,(
% 2.01/0.63    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.63    inference(definition_folding,[],[f37,f46,f45,f44])).
% 2.01/0.63  fof(f45,plain,(
% 2.01/0.63    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 2.01/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.01/0.63  fof(f46,plain,(
% 2.01/0.63    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 2.01/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.01/0.63  fof(f37,plain,(
% 2.01/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.63    inference(flattening,[],[f36])).
% 2.01/0.63  fof(f36,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.63    inference(ennf_transformation,[],[f16])).
% 2.01/0.63  fof(f16,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.01/0.63  fof(f447,plain,(
% 2.01/0.63    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP1(X3,X4) | ~sP2(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.01/0.63    inference(superposition,[],[f96,f91])).
% 2.01/0.63  fof(f91,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f34])).
% 2.01/0.63  fof(f34,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.63    inference(ennf_transformation,[],[f15])).
% 2.01/0.63  fof(f15,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.01/0.63  fof(f96,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f60])).
% 2.01/0.63  fof(f60,plain,(
% 2.01/0.63    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 2.01/0.63    inference(rectify,[],[f59])).
% 2.01/0.63  fof(f59,plain,(
% 2.01/0.63    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 2.01/0.63    inference(nnf_transformation,[],[f45])).
% 2.01/0.63  fof(f2169,plain,(
% 2.01/0.63    ~spl8_25 | ~spl8_26 | spl8_2),
% 2.01/0.63    inference(avatar_split_clause,[],[f2168,f117,f723,f719])).
% 2.01/0.63  fof(f723,plain,(
% 2.01/0.63    spl8_26 <=> sP0(sK5,k7_relat_1(sK7,sK6))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 2.01/0.63  fof(f117,plain,(
% 2.01/0.63    spl8_2 <=> v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 2.01/0.63  fof(f2168,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | ~r1_tarski(sK6,k1_relat_1(sK7)) | spl8_2),
% 2.01/0.63    inference(subsumption_resolution,[],[f2082,f146])).
% 2.01/0.63  fof(f146,plain,(
% 2.01/0.63    v1_relat_1(sK7)),
% 2.01/0.63    inference(subsumption_resolution,[],[f144,f71])).
% 2.01/0.63  fof(f71,plain,(
% 2.01/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.01/0.63    inference(cnf_transformation,[],[f10])).
% 2.01/0.63  fof(f10,axiom,(
% 2.01/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.01/0.63  fof(f144,plain,(
% 2.01/0.63    v1_relat_1(sK7) | ~v1_relat_1(k2_zfmisc_1(sK4,sK5))),
% 2.01/0.63    inference(resolution,[],[f69,f64])).
% 2.01/0.63  fof(f69,plain,(
% 2.01/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f23])).
% 2.01/0.63  fof(f23,plain,(
% 2.01/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f7])).
% 2.01/0.63  fof(f7,axiom,(
% 2.01/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.01/0.63  fof(f2082,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | ~r1_tarski(sK6,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | spl8_2),
% 2.01/0.63    inference(resolution,[],[f490,f358])).
% 2.01/0.63  fof(f358,plain,(
% 2.01/0.63    ( ! [X14,X12,X13] : (v1_funct_2(k7_relat_1(X12,X13),X13,X14) | ~sP0(X14,k7_relat_1(X12,X13)) | ~r1_tarski(X13,k1_relat_1(X12)) | ~v1_relat_1(X12)) )),
% 2.01/0.63    inference(superposition,[],[f80,f74])).
% 2.01/0.63  fof(f74,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f28])).
% 2.01/0.63  fof(f28,plain,(
% 2.01/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(flattening,[],[f27])).
% 2.01/0.63  fof(f27,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f12])).
% 2.01/0.63  fof(f12,axiom,(
% 2.01/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 2.01/0.63  fof(f80,plain,(
% 2.01/0.63    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~sP0(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f51])).
% 2.01/0.63  fof(f51,plain,(
% 2.01/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 2.01/0.63    inference(nnf_transformation,[],[f42])).
% 2.01/0.63  fof(f42,plain,(
% 2.01/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~sP0(X0,X1))),
% 2.01/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.01/0.63  fof(f490,plain,(
% 2.01/0.63    ~v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5) | spl8_2),
% 2.01/0.63    inference(subsumption_resolution,[],[f489,f62])).
% 2.01/0.63  fof(f62,plain,(
% 2.01/0.63    v1_funct_1(sK7)),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  fof(f489,plain,(
% 2.01/0.63    ~v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5) | ~v1_funct_1(sK7) | spl8_2),
% 2.01/0.63    inference(subsumption_resolution,[],[f488,f64])).
% 2.01/0.63  fof(f488,plain,(
% 2.01/0.63    ~v1_funct_2(k7_relat_1(sK7,sK6),sK6,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl8_2),
% 2.01/0.63    inference(superposition,[],[f119,f103])).
% 2.01/0.63  fof(f103,plain,(
% 2.01/0.63    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f41])).
% 2.01/0.63  fof(f41,plain,(
% 2.01/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.01/0.63    inference(flattening,[],[f40])).
% 2.01/0.63  fof(f40,plain,(
% 2.01/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.01/0.63    inference(ennf_transformation,[],[f17])).
% 2.01/0.63  fof(f17,axiom,(
% 2.01/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.01/0.63  fof(f119,plain,(
% 2.01/0.63    ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | spl8_2),
% 2.01/0.63    inference(avatar_component_clause,[],[f117])).
% 2.01/0.63  fof(f2162,plain,(
% 2.01/0.63    spl8_31),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f2161])).
% 2.01/0.63  fof(f2161,plain,(
% 2.01/0.63    $false | spl8_31),
% 2.01/0.63    inference(subsumption_resolution,[],[f2158,f146])).
% 2.01/0.63  fof(f2158,plain,(
% 2.01/0.63    ~v1_relat_1(sK7) | spl8_31),
% 2.01/0.63    inference(resolution,[],[f2156,f73])).
% 2.01/0.63  fof(f73,plain,(
% 2.01/0.63    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f26])).
% 2.01/0.63  fof(f26,plain,(
% 2.01/0.63    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f11])).
% 2.01/0.63  fof(f11,axiom,(
% 2.01/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 2.01/0.63  fof(f2156,plain,(
% 2.01/0.63    ~r1_tarski(k7_relat_1(sK7,sK6),sK7) | spl8_31),
% 2.01/0.63    inference(resolution,[],[f2150,f781])).
% 2.01/0.63  fof(f781,plain,(
% 2.01/0.63    ~v5_relat_1(k7_relat_1(sK7,sK6),sK5) | spl8_31),
% 2.01/0.63    inference(avatar_component_clause,[],[f779])).
% 2.01/0.63  fof(f779,plain,(
% 2.01/0.63    spl8_31 <=> v5_relat_1(k7_relat_1(sK7,sK6),sK5)),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 2.01/0.63  fof(f2150,plain,(
% 2.01/0.63    ( ! [X21] : (v5_relat_1(X21,sK5) | ~r1_tarski(X21,sK7)) )),
% 2.01/0.63    inference(resolution,[],[f264,f142])).
% 2.01/0.63  fof(f264,plain,(
% 2.01/0.63    ( ! [X4,X2,X5,X3] : (~r1_tarski(X4,k2_zfmisc_1(X5,X3)) | v5_relat_1(X2,X3) | ~r1_tarski(X2,X4)) )),
% 2.01/0.63    inference(resolution,[],[f206,f102])).
% 2.01/0.63  fof(f206,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X2,X1)) | v5_relat_1(X0,X1)) )),
% 2.01/0.63    inference(resolution,[],[f93,f87])).
% 2.01/0.63  fof(f87,plain,(
% 2.01/0.63    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f54])).
% 2.01/0.63  fof(f93,plain,(
% 2.01/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f35])).
% 2.01/0.63  fof(f35,plain,(
% 2.01/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.01/0.63    inference(ennf_transformation,[],[f14])).
% 2.01/0.63  fof(f14,axiom,(
% 2.01/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.01/0.63  fof(f2064,plain,(
% 2.01/0.63    ~spl8_31 | ~spl8_1 | spl8_26 | ~spl8_32),
% 2.01/0.63    inference(avatar_split_clause,[],[f2063,f783,f723,f113,f779])).
% 2.01/0.63  fof(f113,plain,(
% 2.01/0.63    spl8_1 <=> v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 2.01/0.63  fof(f783,plain,(
% 2.01/0.63    spl8_32 <=> v1_relat_1(k7_relat_1(sK7,sK6))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 2.01/0.63  fof(f2063,plain,(
% 2.01/0.63    ~v5_relat_1(k7_relat_1(sK7,sK6),sK5) | (~spl8_1 | spl8_26 | ~spl8_32)),
% 2.01/0.63    inference(subsumption_resolution,[],[f2062,f784])).
% 2.01/0.63  fof(f784,plain,(
% 2.01/0.63    v1_relat_1(k7_relat_1(sK7,sK6)) | ~spl8_32),
% 2.01/0.63    inference(avatar_component_clause,[],[f783])).
% 2.01/0.63  fof(f2062,plain,(
% 2.01/0.63    ~v1_relat_1(k7_relat_1(sK7,sK6)) | ~v5_relat_1(k7_relat_1(sK7,sK6),sK5) | (~spl8_1 | spl8_26)),
% 2.01/0.63    inference(subsumption_resolution,[],[f2057,f487])).
% 2.01/0.63  fof(f487,plain,(
% 2.01/0.63    v1_funct_1(k7_relat_1(sK7,sK6)) | ~spl8_1),
% 2.01/0.63    inference(subsumption_resolution,[],[f486,f62])).
% 2.01/0.63  fof(f486,plain,(
% 2.01/0.63    v1_funct_1(k7_relat_1(sK7,sK6)) | ~v1_funct_1(sK7) | ~spl8_1),
% 2.01/0.63    inference(subsumption_resolution,[],[f485,f64])).
% 2.01/0.63  fof(f485,plain,(
% 2.01/0.63    v1_funct_1(k7_relat_1(sK7,sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | ~spl8_1),
% 2.01/0.63    inference(superposition,[],[f114,f103])).
% 2.01/0.63  fof(f114,plain,(
% 2.01/0.63    v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) | ~spl8_1),
% 2.01/0.63    inference(avatar_component_clause,[],[f113])).
% 2.01/0.63  fof(f2057,plain,(
% 2.01/0.63    ~v1_funct_1(k7_relat_1(sK7,sK6)) | ~v1_relat_1(k7_relat_1(sK7,sK6)) | ~v5_relat_1(k7_relat_1(sK7,sK6),sK5) | spl8_26),
% 2.01/0.63    inference(resolution,[],[f725,f281])).
% 2.01/0.63  fof(f281,plain,(
% 2.01/0.63    ( ! [X0,X1] : (sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 2.01/0.63    inference(duplicate_literal_removal,[],[f278])).
% 2.01/0.63  fof(f278,plain,(
% 2.01/0.63    ( ! [X0,X1] : (sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.01/0.63    inference(resolution,[],[f82,f75])).
% 2.01/0.63  fof(f75,plain,(
% 2.01/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f50])).
% 2.01/0.63  fof(f50,plain,(
% 2.01/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(nnf_transformation,[],[f29])).
% 2.01/0.63  fof(f29,plain,(
% 2.01/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(ennf_transformation,[],[f8])).
% 2.01/0.63  fof(f8,axiom,(
% 2.01/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.01/0.63  fof(f82,plain,(
% 2.01/0.63    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sP0(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f43])).
% 2.01/0.63  fof(f43,plain,(
% 2.01/0.63    ! [X0,X1] : (sP0(X0,X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(definition_folding,[],[f33,f42])).
% 2.01/0.63  fof(f33,plain,(
% 2.01/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.01/0.63    inference(flattening,[],[f32])).
% 2.01/0.63  fof(f32,plain,(
% 2.01/0.63    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.01/0.63    inference(ennf_transformation,[],[f18])).
% 2.01/0.63  fof(f18,axiom,(
% 2.01/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 2.01/0.63  fof(f725,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | spl8_26),
% 2.01/0.63    inference(avatar_component_clause,[],[f723])).
% 2.01/0.63  fof(f2055,plain,(
% 2.01/0.63    ~spl8_26 | spl8_2 | ~spl8_29),
% 2.01/0.63    inference(avatar_split_clause,[],[f976,f755,f117,f723])).
% 2.01/0.63  fof(f976,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | (spl8_2 | ~spl8_29)),
% 2.01/0.63    inference(subsumption_resolution,[],[f975,f65])).
% 2.01/0.63  fof(f975,plain,(
% 2.01/0.63    ~r1_tarski(sK6,sK4) | ~sP0(sK5,k7_relat_1(sK7,sK6)) | (spl8_2 | ~spl8_29)),
% 2.01/0.63    inference(forward_demodulation,[],[f974,f757])).
% 2.01/0.63  fof(f757,plain,(
% 2.01/0.63    sK4 = k1_relat_1(sK7) | ~spl8_29),
% 2.01/0.63    inference(avatar_component_clause,[],[f755])).
% 2.01/0.63  fof(f974,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | ~r1_tarski(sK6,k1_relat_1(sK7)) | spl8_2),
% 2.01/0.63    inference(subsumption_resolution,[],[f973,f146])).
% 2.01/0.63  fof(f973,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | ~r1_tarski(sK6,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | spl8_2),
% 2.01/0.63    inference(resolution,[],[f490,f358])).
% 2.01/0.63  fof(f2052,plain,(
% 2.01/0.63    spl8_3 | ~spl8_26 | ~spl8_29),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f2051])).
% 2.01/0.63  fof(f2051,plain,(
% 2.01/0.63    $false | (spl8_3 | ~spl8_26 | ~spl8_29)),
% 2.01/0.63    inference(subsumption_resolution,[],[f2050,f65])).
% 2.01/0.63  fof(f2050,plain,(
% 2.01/0.63    ~r1_tarski(sK6,sK4) | (spl8_3 | ~spl8_26 | ~spl8_29)),
% 2.01/0.63    inference(forward_demodulation,[],[f2049,f757])).
% 2.01/0.63  fof(f2049,plain,(
% 2.01/0.63    ~r1_tarski(sK6,k1_relat_1(sK7)) | (spl8_3 | ~spl8_26)),
% 2.01/0.63    inference(subsumption_resolution,[],[f2048,f146])).
% 2.01/0.63  fof(f2048,plain,(
% 2.01/0.63    ~r1_tarski(sK6,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | (spl8_3 | ~spl8_26)),
% 2.01/0.63    inference(subsumption_resolution,[],[f2045,f724])).
% 2.01/0.63  fof(f724,plain,(
% 2.01/0.63    sP0(sK5,k7_relat_1(sK7,sK6)) | ~spl8_26),
% 2.01/0.63    inference(avatar_component_clause,[],[f723])).
% 2.01/0.63  fof(f2045,plain,(
% 2.01/0.63    ~sP0(sK5,k7_relat_1(sK7,sK6)) | ~r1_tarski(sK6,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | spl8_3),
% 2.01/0.63    inference(resolution,[],[f2044,f357])).
% 2.01/0.63  fof(f357,plain,(
% 2.01/0.63    ( ! [X10,X11,X9] : (m1_subset_1(k7_relat_1(X9,X10),k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~sP0(X11,k7_relat_1(X9,X10)) | ~r1_tarski(X10,k1_relat_1(X9)) | ~v1_relat_1(X9)) )),
% 2.01/0.63    inference(superposition,[],[f81,f74])).
% 2.01/0.63  fof(f81,plain,(
% 2.01/0.63    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~sP0(X0,X1)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f51])).
% 2.01/0.63  fof(f2044,plain,(
% 2.01/0.63    ~m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | spl8_3),
% 2.01/0.63    inference(subsumption_resolution,[],[f2043,f62])).
% 2.01/0.63  fof(f2043,plain,(
% 2.01/0.63    ~m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_1(sK7) | spl8_3),
% 2.01/0.63    inference(subsumption_resolution,[],[f2042,f64])).
% 2.01/0.63  fof(f2042,plain,(
% 2.01/0.63    ~m1_subset_1(k7_relat_1(sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl8_3),
% 2.01/0.63    inference(superposition,[],[f123,f103])).
% 2.01/0.63  fof(f123,plain,(
% 2.01/0.63    ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | spl8_3),
% 2.01/0.63    inference(avatar_component_clause,[],[f121])).
% 2.01/0.63  fof(f121,plain,(
% 2.01/0.63    spl8_3 <=> m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 2.01/0.63  fof(f1920,plain,(
% 2.01/0.63    spl8_3 | ~spl8_9 | ~spl8_11),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f1919])).
% 2.01/0.63  fof(f1919,plain,(
% 2.01/0.63    $false | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1916,f146])).
% 2.01/0.63  fof(f1916,plain,(
% 2.01/0.63    ~v1_relat_1(sK7) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(resolution,[],[f1914,f73])).
% 2.01/0.63  fof(f1914,plain,(
% 2.01/0.63    ~r1_tarski(k7_relat_1(sK7,sK4),sK7) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(resolution,[],[f1890,f87])).
% 2.01/0.63  fof(f1890,plain,(
% 2.01/0.63    ~m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7)) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1889,f1837])).
% 2.01/0.63  fof(f1837,plain,(
% 2.01/0.63    m1_subset_1(sK7,k1_zfmisc_1(sK7)) | ~spl8_11),
% 2.01/0.63    inference(backward_demodulation,[],[f64,f190])).
% 2.01/0.63  fof(f190,plain,(
% 2.01/0.63    sK7 = k2_zfmisc_1(sK4,sK5) | ~spl8_11),
% 2.01/0.63    inference(avatar_component_clause,[],[f188])).
% 2.01/0.63  fof(f1889,plain,(
% 2.01/0.63    ~m1_subset_1(sK7,k1_zfmisc_1(sK7)) | ~m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7)) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(forward_demodulation,[],[f1888,f190])).
% 2.01/0.63  fof(f1888,plain,(
% 2.01/0.63    ~m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1887,f62])).
% 2.01/0.63  fof(f1887,plain,(
% 2.01/0.63    ~m1_subset_1(k7_relat_1(sK7,sK4),k1_zfmisc_1(sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(superposition,[],[f1872,f103])).
% 2.01/0.63  fof(f1872,plain,(
% 2.01/0.63    ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK4),k1_zfmisc_1(sK7)) | (spl8_3 | ~spl8_9 | ~spl8_11)),
% 2.01/0.63    inference(forward_demodulation,[],[f1871,f190])).
% 2.01/0.63  fof(f1871,plain,(
% 2.01/0.63    ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK4),k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | (spl8_3 | ~spl8_9)),
% 2.01/0.63    inference(forward_demodulation,[],[f123,f181])).
% 2.01/0.63  fof(f181,plain,(
% 2.01/0.63    sK4 = sK6 | ~spl8_9),
% 2.01/0.63    inference(avatar_component_clause,[],[f179])).
% 2.01/0.63  fof(f1474,plain,(
% 2.01/0.63    ~spl8_5 | spl8_13),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f1473])).
% 2.01/0.63  fof(f1473,plain,(
% 2.01/0.63    $false | (~spl8_5 | spl8_13)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1432,f68])).
% 2.01/0.63  fof(f1432,plain,(
% 2.01/0.63    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl8_5 | spl8_13)),
% 2.01/0.63    inference(backward_demodulation,[],[f317,f132])).
% 2.01/0.63  fof(f132,plain,(
% 2.01/0.63    k1_xboole_0 = sK4 | ~spl8_5),
% 2.01/0.63    inference(avatar_component_clause,[],[f130])).
% 2.01/0.63  fof(f130,plain,(
% 2.01/0.63    spl8_5 <=> k1_xboole_0 = sK4),
% 2.01/0.63    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 2.01/0.63  fof(f317,plain,(
% 2.01/0.63    ~r1_tarski(sK4,k1_xboole_0) | spl8_13),
% 2.01/0.63    inference(avatar_component_clause,[],[f315])).
% 2.01/0.63  fof(f1466,plain,(
% 2.01/0.63    ~spl8_5 | spl8_8),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f1465])).
% 2.01/0.63  fof(f1465,plain,(
% 2.01/0.63    $false | (~spl8_5 | spl8_8)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1424,f68])).
% 2.01/0.63  fof(f1424,plain,(
% 2.01/0.63    ~r1_tarski(k1_xboole_0,sK6) | (~spl8_5 | spl8_8)),
% 2.01/0.63    inference(backward_demodulation,[],[f177,f132])).
% 2.01/0.63  fof(f177,plain,(
% 2.01/0.63    ~r1_tarski(sK4,sK6) | spl8_8),
% 2.01/0.63    inference(avatar_component_clause,[],[f175])).
% 2.01/0.63  fof(f1333,plain,(
% 2.01/0.63    ~spl8_4 | spl8_10),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f1332])).
% 2.01/0.63  fof(f1332,plain,(
% 2.01/0.63    $false | (~spl8_4 | spl8_10)),
% 2.01/0.63    inference(subsumption_resolution,[],[f1331,f68])).
% 2.01/0.63  fof(f1331,plain,(
% 2.01/0.63    ~r1_tarski(k1_xboole_0,sK7) | (~spl8_4 | spl8_10)),
% 2.01/0.63    inference(forward_demodulation,[],[f1302,f106])).
% 2.01/0.63  fof(f106,plain,(
% 2.01/0.63    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.01/0.63    inference(equality_resolution,[],[f90])).
% 2.01/0.63  fof(f90,plain,(
% 2.01/0.63    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.01/0.63    inference(cnf_transformation,[],[f56])).
% 2.01/0.63  fof(f56,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.01/0.63    inference(flattening,[],[f55])).
% 2.01/0.63  fof(f55,plain,(
% 2.01/0.63    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.01/0.63    inference(nnf_transformation,[],[f5])).
% 2.01/0.63  fof(f5,axiom,(
% 2.01/0.63    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.01/0.63  fof(f1302,plain,(
% 2.01/0.63    ~r1_tarski(k2_zfmisc_1(sK4,k1_xboole_0),sK7) | (~spl8_4 | spl8_10)),
% 2.01/0.63    inference(backward_demodulation,[],[f186,f127])).
% 2.01/0.63  fof(f127,plain,(
% 2.01/0.63    k1_xboole_0 = sK5 | ~spl8_4),
% 2.01/0.63    inference(avatar_component_clause,[],[f126])).
% 2.01/0.63  fof(f186,plain,(
% 2.01/0.63    ~r1_tarski(k2_zfmisc_1(sK4,sK5),sK7) | spl8_10),
% 2.01/0.63    inference(avatar_component_clause,[],[f184])).
% 2.01/0.63  fof(f796,plain,(
% 2.01/0.63    spl8_32),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f795])).
% 2.01/0.63  fof(f795,plain,(
% 2.01/0.63    $false | spl8_32),
% 2.01/0.63    inference(subsumption_resolution,[],[f794,f146])).
% 2.01/0.63  fof(f794,plain,(
% 2.01/0.63    ~v1_relat_1(sK7) | spl8_32),
% 2.01/0.63    inference(resolution,[],[f785,f72])).
% 2.01/0.63  fof(f72,plain,(
% 2.01/0.63    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f25])).
% 2.01/0.63  fof(f25,plain,(
% 2.01/0.63    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.01/0.63    inference(ennf_transformation,[],[f9])).
% 2.01/0.63  fof(f9,axiom,(
% 2.01/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.01/0.63  fof(f785,plain,(
% 2.01/0.63    ~v1_relat_1(k7_relat_1(sK7,sK6)) | spl8_32),
% 2.01/0.63    inference(avatar_component_clause,[],[f783])).
% 2.01/0.63  fof(f484,plain,(
% 2.01/0.63    spl8_1),
% 2.01/0.63    inference(avatar_contradiction_clause,[],[f483])).
% 2.01/0.63  fof(f483,plain,(
% 2.01/0.63    $false | spl8_1),
% 2.01/0.63    inference(subsumption_resolution,[],[f482,f146])).
% 2.01/0.63  fof(f482,plain,(
% 2.01/0.63    ~v1_relat_1(sK7) | spl8_1),
% 2.01/0.63    inference(subsumption_resolution,[],[f481,f62])).
% 2.01/0.63  fof(f481,plain,(
% 2.01/0.63    ~v1_funct_1(sK7) | ~v1_relat_1(sK7) | spl8_1),
% 2.01/0.63    inference(resolution,[],[f480,f78])).
% 2.01/0.63  fof(f78,plain,(
% 2.01/0.63    ( ! [X0,X1] : (v1_funct_1(k7_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.01/0.63    inference(cnf_transformation,[],[f31])).
% 2.01/0.63  fof(f31,plain,(
% 2.01/0.63    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.01/0.63    inference(flattening,[],[f30])).
% 2.01/0.63  fof(f30,plain,(
% 2.01/0.63    ! [X0,X1] : ((v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.01/0.63    inference(ennf_transformation,[],[f13])).
% 2.01/0.63  fof(f13,axiom,(
% 2.01/0.63    ! [X0,X1] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k7_relat_1(X0,X1)) & v1_relat_1(k7_relat_1(X0,X1))))),
% 2.01/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).
% 2.01/0.63  fof(f480,plain,(
% 2.01/0.63    ~v1_funct_1(k7_relat_1(sK7,sK6)) | spl8_1),
% 2.01/0.63    inference(subsumption_resolution,[],[f479,f62])).
% 2.01/0.63  fof(f479,plain,(
% 2.01/0.63    ~v1_funct_1(k7_relat_1(sK7,sK6)) | ~v1_funct_1(sK7) | spl8_1),
% 2.01/0.63    inference(subsumption_resolution,[],[f478,f64])).
% 2.01/0.63  fof(f478,plain,(
% 2.01/0.63    ~v1_funct_1(k7_relat_1(sK7,sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) | ~v1_funct_1(sK7) | spl8_1),
% 2.01/0.63    inference(superposition,[],[f115,f103])).
% 2.01/0.63  fof(f115,plain,(
% 2.01/0.63    ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6)) | spl8_1),
% 2.01/0.63    inference(avatar_component_clause,[],[f113])).
% 2.01/0.63  fof(f133,plain,(
% 2.01/0.63    ~spl8_4 | spl8_5),
% 2.01/0.63    inference(avatar_split_clause,[],[f66,f130,f126])).
% 2.01/0.63  fof(f66,plain,(
% 2.01/0.63    k1_xboole_0 = sK4 | k1_xboole_0 != sK5),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  fof(f124,plain,(
% 2.01/0.63    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 2.01/0.63    inference(avatar_split_clause,[],[f67,f121,f117,f113])).
% 2.01/0.63  fof(f67,plain,(
% 2.01/0.63    ~m1_subset_1(k2_partfun1(sK4,sK5,sK7,sK6),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) | ~v1_funct_2(k2_partfun1(sK4,sK5,sK7,sK6),sK6,sK5) | ~v1_funct_1(k2_partfun1(sK4,sK5,sK7,sK6))),
% 2.01/0.63    inference(cnf_transformation,[],[f49])).
% 2.01/0.63  % SZS output end Proof for theBenchmark
% 2.01/0.63  % (27664)------------------------------
% 2.01/0.63  % (27664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.63  % (27664)Termination reason: Refutation
% 2.01/0.63  
% 2.01/0.63  % (27664)Memory used [KB]: 7036
% 2.01/0.63  % (27664)Time elapsed: 0.190 s
% 2.01/0.63  % (27664)------------------------------
% 2.01/0.63  % (27664)------------------------------
% 2.01/0.63  % (27659)Success in time 0.264 s
%------------------------------------------------------------------------------
