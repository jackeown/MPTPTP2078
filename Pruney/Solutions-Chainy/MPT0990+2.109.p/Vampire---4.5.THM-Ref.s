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
% DateTime   : Thu Dec  3 13:02:47 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 573 expanded)
%              Number of leaves         :   54 ( 213 expanded)
%              Depth                    :   11
%              Number of atoms          :  790 (2172 expanded)
%              Number of equality atoms :  141 ( 582 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f137,f146,f150,f156,f206,f208,f276,f278,f289,f292,f388,f405,f428,f535,f576,f583,f710,f712,f876,f1053,f1175,f1225,f1233,f1396,f1427,f1441,f1656,f1682,f1752,f1878,f2226,f2268,f2380])).

fof(f2380,plain,(
    ~ spl4_198 ),
    inference(avatar_contradiction_clause,[],[f2321])).

fof(f2321,plain,
    ( $false
    | ~ spl4_198 ),
    inference(subsumption_resolution,[],[f71,f2258])).

fof(f2258,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_198 ),
    inference(avatar_component_clause,[],[f2256])).

fof(f2256,plain,
    ( spl4_198
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f71,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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

fof(f2268,plain,
    ( ~ spl4_9
    | spl4_198
    | ~ spl4_164
    | ~ spl4_69
    | ~ spl4_125
    | ~ spl4_196 ),
    inference(avatar_split_clause,[],[f2267,f2223,f1408,f869,f1862,f2256,f269])).

fof(f269,plain,
    ( spl4_9
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f1862,plain,
    ( spl4_164
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f869,plain,
    ( spl4_69
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f1408,plain,
    ( spl4_125
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).

fof(f2223,plain,
    ( spl4_196
  <=> sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f2267,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_69
    | ~ spl4_125
    | ~ spl4_196 ),
    inference(forward_demodulation,[],[f2266,f1490])).

fof(f1490,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_125 ),
    inference(forward_demodulation,[],[f1459,f116])).

fof(f116,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f75])).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1459,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_125 ),
    inference(superposition,[],[f116,f1410])).

fof(f1410,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_125 ),
    inference(avatar_component_clause,[],[f1408])).

fof(f2266,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | sK3 = k2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_69
    | ~ spl4_196 ),
    inference(forward_demodulation,[],[f2248,f870])).

fof(f870,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f869])).

fof(f2248,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_196 ),
    inference(superposition,[],[f121,f2225])).

fof(f2225,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_196 ),
    inference(avatar_component_clause,[],[f2223])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f97,f75])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f2226,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_1
    | ~ spl4_3
    | spl4_196
    | ~ spl4_6
    | ~ spl4_109
    | ~ spl4_160 ),
    inference(avatar_split_clause,[],[f2221,f1749,f1181,f202,f2223,f139,f130,f269,f265,f261])).

fof(f261,plain,
    ( spl4_7
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f265,plain,
    ( spl4_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f130,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f139,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f202,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1181,plain,
    ( spl4_109
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).

fof(f1749,plain,
    ( spl4_160
  <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f2221,plain,
    ( sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_109
    | ~ spl4_160 ),
    inference(forward_demodulation,[],[f2220,f1751])).

fof(f1751,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_160 ),
    inference(avatar_component_clause,[],[f1749])).

fof(f2220,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_109 ),
    inference(forward_demodulation,[],[f2117,f204])).

fof(f204,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f202])).

fof(f2117,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_109 ),
    inference(superposition,[],[f317,f1183])).

fof(f1183,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_109 ),
    inference(avatar_component_clause,[],[f1181])).

fof(f317,plain,(
    ! [X10,X9] :
      ( k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k2_funct_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X10,X9] :
      ( k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10)
      | ~ v1_relat_1(X9)
      | ~ v1_relat_1(X10)
      | ~ v1_relat_1(k2_funct_1(X9))
      | ~ v1_funct_1(X9)
      | ~ v2_funct_1(X9)
      | ~ v1_relat_1(X9) ) ),
    inference(superposition,[],[f84,f119])).

fof(f119,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f92,f75])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1878,plain,(
    spl4_164 ),
    inference(avatar_contradiction_clause,[],[f1874])).

fof(f1874,plain,
    ( $false
    | spl4_164 ),
    inference(unit_resulting_resolution,[],[f115,f165,f1864,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f99,f117])).

fof(f117,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f80,f75])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f1864,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_164 ),
    inference(avatar_component_clause,[],[f1862])).

fof(f165,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f76,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1752,plain,
    ( ~ spl4_1
    | spl4_160
    | ~ spl4_31
    | ~ spl4_125
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f1730,f1649,f1408,f569,f1749,f130])).

fof(f569,plain,
    ( spl4_31
  <=> sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1649,plain,
    ( spl4_150
  <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f1730,plain,
    ( sK3 = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_31
    | ~ spl4_125
    | ~ spl4_150 ),
    inference(superposition,[],[f118,f1724])).

fof(f1724,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_31
    | ~ spl4_125
    | ~ spl4_150 ),
    inference(forward_demodulation,[],[f1651,f1541])).

fof(f1541,plain,
    ( sK1 = k9_relat_1(sK2,sK0)
    | ~ spl4_31
    | ~ spl4_125 ),
    inference(superposition,[],[f571,f1490])).

fof(f571,plain,
    ( sK1 = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f569])).

fof(f1651,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ spl4_150 ),
    inference(avatar_component_clause,[],[f1649])).

fof(f118,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f75])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f1682,plain,
    ( ~ spl4_1
    | spl4_151 ),
    inference(avatar_contradiction_clause,[],[f1680])).

fof(f1680,plain,
    ( $false
    | ~ spl4_1
    | spl4_151 ),
    inference(unit_resulting_resolution,[],[f132,f163,f1655,f99])).

fof(f1655,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_151 ),
    inference(avatar_component_clause,[],[f1653])).

fof(f1653,plain,
    ( spl4_151
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).

fof(f163,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f106,f65])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f132,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1656,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_8
    | spl4_150
    | ~ spl4_151
    | ~ spl4_6
    | ~ spl4_109 ),
    inference(avatar_split_clause,[],[f1647,f1181,f202,f1653,f1649,f265,f139,f130])).

fof(f1647,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_6
    | ~ spl4_109 ),
    inference(forward_demodulation,[],[f1646,f204])).

fof(f1646,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,sK0)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_109 ),
    inference(forward_demodulation,[],[f1593,f117])).

fof(f1593,plain,
    ( k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl4_109 ),
    inference(superposition,[],[f286,f1183])).

fof(f286,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ r1_tarski(k1_relat_1(X1),k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f100,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

fof(f1441,plain,
    ( ~ spl4_3
    | spl4_126 ),
    inference(avatar_contradiction_clause,[],[f1439])).

fof(f1439,plain,
    ( $false
    | ~ spl4_3
    | spl4_126 ),
    inference(unit_resulting_resolution,[],[f141,f164,f1414,f99])).

fof(f1414,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_126 ),
    inference(avatar_component_clause,[],[f1412])).

fof(f1412,plain,
    ( spl4_126
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f164,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f106,f74])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1427,plain,
    ( ~ spl4_92
    | spl4_125
    | ~ spl4_126
    | ~ spl4_123 ),
    inference(avatar_split_clause,[],[f1426,f1393,f1412,f1408,f1040])).

fof(f1040,plain,
    ( spl4_92
  <=> v1_relat_1(k6_partfun1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f1393,plain,
    ( spl4_123
  <=> k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).

fof(f1426,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_123 ),
    inference(forward_demodulation,[],[f1403,f116])).

fof(f1403,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(k6_partfun1(k1_relat_1(sK2))),sK0)
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_123 ),
    inference(superposition,[],[f121,f1395])).

fof(f1395,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0))
    | ~ spl4_123 ),
    inference(avatar_component_clause,[],[f1393])).

fof(f1396,plain,
    ( ~ spl4_92
    | ~ spl4_1
    | ~ spl4_3
    | spl4_123
    | ~ spl4_109 ),
    inference(avatar_split_clause,[],[f1365,f1181,f1393,f139,f130,f1040])).

fof(f1365,plain,
    ( k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_109 ),
    inference(superposition,[],[f316,f1183])).

fof(f316,plain,(
    ! [X12,X11] :
      ( k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(X11))) ) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,(
    ! [X12,X11] :
      ( k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12))
      | ~ v1_relat_1(X11)
      | ~ v1_relat_1(X12)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(X11)))
      | ~ v1_relat_1(X11) ) ),
    inference(superposition,[],[f84,f118])).

fof(f1233,plain,
    ( ~ spl4_8
    | ~ spl4_45
    | ~ spl4_46
    | ~ spl4_5
    | spl4_109
    | ~ spl4_107 ),
    inference(avatar_split_clause,[],[f1229,f1172,f1181,f198,f695,f691,f265])).

fof(f691,plain,
    ( spl4_45
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f695,plain,
    ( spl4_46
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f198,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1172,plain,
    ( spl4_107
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).

fof(f1229,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_107 ),
    inference(superposition,[],[f111,f1174])).

fof(f1174,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_107 ),
    inference(avatar_component_clause,[],[f1172])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1225,plain,(
    spl4_106 ),
    inference(avatar_contradiction_clause,[],[f1222])).

fof(f1222,plain,
    ( $false
    | spl4_106 ),
    inference(unit_resulting_resolution,[],[f72,f63,f65,f74,f1170,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1170,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_106 ),
    inference(avatar_component_clause,[],[f1168])).

fof(f1168,plain,
    ( spl4_106
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f1175,plain,
    ( ~ spl4_106
    | spl4_107 ),
    inference(avatar_split_clause,[],[f1164,f1172,f1168])).

fof(f1164,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f564,f67])).

fof(f67,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f564,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f110,f79])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1053,plain,(
    spl4_92 ),
    inference(avatar_contradiction_clause,[],[f1049])).

fof(f1049,plain,
    ( $false
    | spl4_92 ),
    inference(unit_resulting_resolution,[],[f95,f79,f1042,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1042,plain,
    ( ~ v1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | spl4_92 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f876,plain,
    ( ~ spl4_3
    | spl4_69 ),
    inference(avatar_contradiction_clause,[],[f873])).

fof(f873,plain,
    ( $false
    | ~ spl4_3
    | spl4_69 ),
    inference(unit_resulting_resolution,[],[f141,f68,f72,f871,f90])).

fof(f90,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f871,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f869])).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f712,plain,(
    spl4_46 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | spl4_46 ),
    inference(subsumption_resolution,[],[f63,f697])).

fof(f697,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f695])).

fof(f710,plain,(
    spl4_45 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | spl4_45 ),
    inference(subsumption_resolution,[],[f65,f693])).

fof(f693,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f691])).

fof(f583,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | spl4_32 ),
    inference(unit_resulting_resolution,[],[f115,f165,f575,f159])).

fof(f575,plain,
    ( ~ r1_tarski(sK1,sK1)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl4_32
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f576,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | spl4_31
    | ~ spl4_32
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f567,f532,f202,f573,f569,f265,f139])).

fof(f532,plain,
    ( spl4_27
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f567,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f566,f204])).

fof(f566,plain,
    ( sK1 = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_27 ),
    inference(superposition,[],[f100,f534])).

fof(f534,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f532])).

fof(f535,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_3
    | spl4_27
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f530,f426,f532,f139,f265,f261])).

fof(f426,plain,
    ( spl4_14
  <=> ! [X0] :
        ( k1_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f530,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f529,f117])).

fof(f529,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_14 ),
    inference(duplicate_literal_removal,[],[f511])).

fof(f511,plain,
    ( k10_relat_1(sK2,sK1) = k1_relat_1(k6_partfun1(k1_relat_1(sK2)))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(superposition,[],[f427,f120])).

fof(f120,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f91,f75])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f427,plain,
    ( ! [X0] :
        ( k1_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(X0,sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f426])).

fof(f428,plain,
    ( ~ spl4_9
    | spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f416,f402,f426,f269])).

fof(f402,plain,
    ( spl4_12
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f416,plain,
    ( ! [X0] :
        ( k1_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(X0,sK1)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f83,f404])).

fof(f404,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f402])).

fof(f405,plain,
    ( ~ spl4_10
    | ~ spl4_9
    | spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f398,f385,f402,f269,f273])).

fof(f273,plain,
    ( spl4_10
  <=> v4_relat_1(k2_funct_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f385,plain,
    ( spl4_11
  <=> r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f398,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v4_relat_1(k2_funct_1(sK2),sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f387,f162])).

fof(f162,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X2))
      | k1_relat_1(X2) = X1
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X1) ) ),
    inference(resolution,[],[f104,f99])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f387,plain,
    ( r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f385])).

fof(f388,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f378,f202,f385,f269,f265,f261,f139])).

fof(f378,plain,
    ( r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f370,f204])).

fof(f370,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1)))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k2_funct_1(X1))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X1)) ) ),
    inference(resolution,[],[f187,f151])).

fof(f151,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f98,f122])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f187,plain,(
    ! [X2,X1] :
      ( ~ v4_relat_1(k2_funct_1(X1),X2)
      | ~ v1_relat_1(k2_funct_1(X1))
      | r1_tarski(k2_relat_1(X1),X2)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f99,f89])).

fof(f89,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f292,plain,
    ( ~ spl4_3
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | ~ spl4_3
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f141,f72,f271,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f271,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f269])).

fof(f289,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f72,f267])).

fof(f267,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f265])).

fof(f278,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f68,f263])).

fof(f263,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f261])).

fof(f276,plain,
    ( ~ spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f258,f202,f273,f269,f265,f261,f139])).

fof(f258,plain,
    ( v4_relat_1(k2_funct_1(sK2),sK1)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f188,f204])).

fof(f188,plain,(
    ! [X3] :
      ( v4_relat_1(k2_funct_1(X3),k2_relat_1(X3))
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v2_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f151,f89])).

fof(f208,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f74,f200])).

fof(f200,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f198])).

fof(f206,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f196,f202,f198])).

fof(f196,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f66,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f66,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f156,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f95,f145])).

fof(f145,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f150,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f95,f136])).

fof(f136,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f146,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f127,f143,f139])).

fof(f127,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f85,f74])).

fof(f137,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f126,f134,f130])).

fof(f126,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f85,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (5984)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.15/0.51  % (5987)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.15/0.51  % (5985)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.15/0.52  % (6000)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.15/0.52  % (5986)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.15/0.52  % (5988)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.15/0.53  % (6006)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.31/0.53  % (6010)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.31/0.53  % (5992)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.31/0.53  % (5994)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.31/0.53  % (5997)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.31/0.53  % (6005)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.31/0.53  % (5993)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.31/0.53  % (6007)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.31/0.53  % (6011)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.31/0.54  % (6008)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.31/0.54  % (5989)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.31/0.54  % (5999)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.31/0.54  % (6012)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.31/0.54  % (5982)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.31/0.54  % (5996)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.31/0.54  % (6003)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.31/0.54  % (5995)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.31/0.54  % (5983)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.31/0.54  % (5991)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.31/0.54  % (5990)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.31/0.55  % (6009)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.31/0.55  % (6001)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.31/0.56  % (6002)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.31/0.56  % (5998)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.31/0.58  % (5998)Refutation not found, incomplete strategy% (5998)------------------------------
% 1.31/0.58  % (5998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.58  % (5998)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.58  
% 1.31/0.58  % (5998)Memory used [KB]: 10746
% 1.31/0.58  % (5998)Time elapsed: 0.179 s
% 1.31/0.58  % (5998)------------------------------
% 1.31/0.58  % (5998)------------------------------
% 2.02/0.66  % (6120)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.02/0.66  % (5995)Refutation found. Thanks to Tanya!
% 2.02/0.66  % SZS status Theorem for theBenchmark
% 2.02/0.66  % SZS output start Proof for theBenchmark
% 2.02/0.66  fof(f2402,plain,(
% 2.02/0.66    $false),
% 2.02/0.66    inference(avatar_sat_refutation,[],[f137,f146,f150,f156,f206,f208,f276,f278,f289,f292,f388,f405,f428,f535,f576,f583,f710,f712,f876,f1053,f1175,f1225,f1233,f1396,f1427,f1441,f1656,f1682,f1752,f1878,f2226,f2268,f2380])).
% 2.02/0.66  fof(f2380,plain,(
% 2.02/0.66    ~spl4_198),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f2321])).
% 2.02/0.66  fof(f2321,plain,(
% 2.02/0.66    $false | ~spl4_198),
% 2.02/0.66    inference(subsumption_resolution,[],[f71,f2258])).
% 2.02/0.66  fof(f2258,plain,(
% 2.02/0.66    sK3 = k2_funct_1(sK2) | ~spl4_198),
% 2.02/0.66    inference(avatar_component_clause,[],[f2256])).
% 2.02/0.66  fof(f2256,plain,(
% 2.02/0.66    spl4_198 <=> sK3 = k2_funct_1(sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).
% 2.02/0.66  fof(f71,plain,(
% 2.02/0.66    sK3 != k2_funct_1(sK2)),
% 2.02/0.66    inference(cnf_transformation,[],[f30])).
% 2.02/0.66  fof(f30,plain,(
% 2.02/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.02/0.66    inference(flattening,[],[f29])).
% 2.02/0.66  fof(f29,plain,(
% 2.02/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.02/0.66    inference(ennf_transformation,[],[f28])).
% 2.02/0.66  fof(f28,negated_conjecture,(
% 2.02/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.02/0.66    inference(negated_conjecture,[],[f27])).
% 2.02/0.66  fof(f27,conjecture,(
% 2.02/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.02/0.66  fof(f2268,plain,(
% 2.02/0.66    ~spl4_9 | spl4_198 | ~spl4_164 | ~spl4_69 | ~spl4_125 | ~spl4_196),
% 2.02/0.66    inference(avatar_split_clause,[],[f2267,f2223,f1408,f869,f1862,f2256,f269])).
% 2.02/0.66  fof(f269,plain,(
% 2.02/0.66    spl4_9 <=> v1_relat_1(k2_funct_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.02/0.66  fof(f1862,plain,(
% 2.02/0.66    spl4_164 <=> r1_tarski(sK0,sK0)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).
% 2.02/0.66  fof(f869,plain,(
% 2.02/0.66    spl4_69 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 2.02/0.66  fof(f1408,plain,(
% 2.02/0.66    spl4_125 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).
% 2.02/0.66  fof(f2223,plain,(
% 2.02/0.66    spl4_196 <=> sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).
% 2.02/0.66  fof(f2267,plain,(
% 2.02/0.66    ~r1_tarski(sK0,sK0) | sK3 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_69 | ~spl4_125 | ~spl4_196)),
% 2.02/0.66    inference(forward_demodulation,[],[f2266,f1490])).
% 2.02/0.66  fof(f1490,plain,(
% 2.02/0.66    sK0 = k1_relat_1(sK2) | ~spl4_125),
% 2.02/0.66    inference(forward_demodulation,[],[f1459,f116])).
% 2.02/0.66  fof(f116,plain,(
% 2.02/0.66    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.02/0.66    inference(definition_unfolding,[],[f81,f75])).
% 2.02/0.66  fof(f75,plain,(
% 2.02/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f25])).
% 2.02/0.66  fof(f25,axiom,(
% 2.02/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.02/0.66  fof(f81,plain,(
% 2.02/0.66    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.02/0.66    inference(cnf_transformation,[],[f9])).
% 2.02/0.66  fof(f9,axiom,(
% 2.02/0.66    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.02/0.66  fof(f1459,plain,(
% 2.02/0.66    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_125),
% 2.02/0.66    inference(superposition,[],[f116,f1410])).
% 2.02/0.66  fof(f1410,plain,(
% 2.02/0.66    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_125),
% 2.02/0.66    inference(avatar_component_clause,[],[f1408])).
% 2.02/0.66  fof(f2266,plain,(
% 2.02/0.66    ~r1_tarski(k1_relat_1(sK2),sK0) | sK3 = k2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_69 | ~spl4_196)),
% 2.02/0.66    inference(forward_demodulation,[],[f2248,f870])).
% 2.02/0.66  fof(f870,plain,(
% 2.02/0.66    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_69),
% 2.02/0.66    inference(avatar_component_clause,[],[f869])).
% 2.02/0.66  fof(f2248,plain,(
% 2.02/0.66    sK3 = k2_funct_1(sK2) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_196),
% 2.02/0.66    inference(superposition,[],[f121,f2225])).
% 2.02/0.66  fof(f2225,plain,(
% 2.02/0.66    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_196),
% 2.02/0.66    inference(avatar_component_clause,[],[f2223])).
% 2.02/0.66  fof(f121,plain,(
% 2.02/0.66    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.02/0.66    inference(definition_unfolding,[],[f97,f75])).
% 2.02/0.66  fof(f97,plain,(
% 2.02/0.66    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 2.02/0.66    inference(cnf_transformation,[],[f47])).
% 2.02/0.66  fof(f47,plain,(
% 2.02/0.66    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 2.02/0.66    inference(flattening,[],[f46])).
% 2.02/0.66  fof(f46,plain,(
% 2.02/0.66    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.66    inference(ennf_transformation,[],[f11])).
% 2.02/0.66  fof(f11,axiom,(
% 2.02/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 2.02/0.66  fof(f2226,plain,(
% 2.02/0.66    ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_1 | ~spl4_3 | spl4_196 | ~spl4_6 | ~spl4_109 | ~spl4_160),
% 2.02/0.66    inference(avatar_split_clause,[],[f2221,f1749,f1181,f202,f2223,f139,f130,f269,f265,f261])).
% 2.02/0.66  fof(f261,plain,(
% 2.02/0.66    spl4_7 <=> v2_funct_1(sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.02/0.66  fof(f265,plain,(
% 2.02/0.66    spl4_8 <=> v1_funct_1(sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.02/0.66  fof(f130,plain,(
% 2.02/0.66    spl4_1 <=> v1_relat_1(sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.02/0.66  fof(f139,plain,(
% 2.02/0.66    spl4_3 <=> v1_relat_1(sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.02/0.66  fof(f202,plain,(
% 2.02/0.66    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.02/0.66  fof(f1181,plain,(
% 2.02/0.66    spl4_109 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_109])])).
% 2.02/0.66  fof(f1749,plain,(
% 2.02/0.66    spl4_160 <=> sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).
% 2.02/0.66  fof(f2221,plain,(
% 2.02/0.66    sK3 = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_109 | ~spl4_160)),
% 2.02/0.66    inference(forward_demodulation,[],[f2220,f1751])).
% 2.02/0.66  fof(f1751,plain,(
% 2.02/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_160),
% 2.02/0.66    inference(avatar_component_clause,[],[f1749])).
% 2.02/0.66  fof(f2220,plain,(
% 2.02/0.66    k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_109)),
% 2.02/0.66    inference(forward_demodulation,[],[f2117,f204])).
% 2.02/0.66  fof(f204,plain,(
% 2.02/0.66    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 2.02/0.66    inference(avatar_component_clause,[],[f202])).
% 2.02/0.66  fof(f2117,plain,(
% 2.02/0.66    k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_109),
% 2.02/0.66    inference(superposition,[],[f317,f1183])).
% 2.02/0.66  fof(f1183,plain,(
% 2.02/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_109),
% 2.02/0.66    inference(avatar_component_clause,[],[f1181])).
% 2.02/0.66  fof(f317,plain,(
% 2.02/0.66    ( ! [X10,X9] : (k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10) | ~v1_relat_1(X9) | ~v1_relat_1(X10) | ~v1_relat_1(k2_funct_1(X9)) | ~v1_funct_1(X9) | ~v2_funct_1(X9)) )),
% 2.02/0.66    inference(duplicate_literal_removal,[],[f306])).
% 2.02/0.66  fof(f306,plain,(
% 2.02/0.66    ( ! [X10,X9] : (k5_relat_1(k2_funct_1(X9),k5_relat_1(X9,X10)) = k5_relat_1(k6_partfun1(k2_relat_1(X9)),X10) | ~v1_relat_1(X9) | ~v1_relat_1(X10) | ~v1_relat_1(k2_funct_1(X9)) | ~v1_funct_1(X9) | ~v2_funct_1(X9) | ~v1_relat_1(X9)) )),
% 2.02/0.66    inference(superposition,[],[f84,f119])).
% 2.02/0.66  fof(f119,plain,(
% 2.02/0.66    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.66    inference(definition_unfolding,[],[f92,f75])).
% 2.02/0.66  fof(f92,plain,(
% 2.02/0.66    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f42])).
% 2.02/0.66  fof(f42,plain,(
% 2.02/0.66    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.66    inference(flattening,[],[f41])).
% 2.02/0.66  fof(f41,plain,(
% 2.02/0.66    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.66    inference(ennf_transformation,[],[f17])).
% 2.02/0.66  fof(f17,axiom,(
% 2.02/0.66    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.02/0.66  fof(f84,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f33])).
% 2.02/0.66  fof(f33,plain,(
% 2.02/0.66    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.66    inference(ennf_transformation,[],[f8])).
% 2.02/0.66  fof(f8,axiom,(
% 2.02/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.02/0.66  fof(f1878,plain,(
% 2.02/0.66    spl4_164),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f1874])).
% 2.02/0.66  fof(f1874,plain,(
% 2.02/0.66    $false | spl4_164),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f115,f165,f1864,f159])).
% 2.02/0.66  fof(f159,plain,(
% 2.02/0.66    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0)) | r1_tarski(X0,X1)) )),
% 2.02/0.66    inference(superposition,[],[f99,f117])).
% 2.02/0.66  fof(f117,plain,(
% 2.02/0.66    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.02/0.66    inference(definition_unfolding,[],[f80,f75])).
% 2.02/0.66  fof(f80,plain,(
% 2.02/0.66    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.02/0.66    inference(cnf_transformation,[],[f9])).
% 2.02/0.66  fof(f99,plain,(
% 2.02/0.66    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f48])).
% 2.02/0.66  fof(f48,plain,(
% 2.02/0.66    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.02/0.66    inference(ennf_transformation,[],[f3])).
% 2.02/0.66  fof(f3,axiom,(
% 2.02/0.66    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.02/0.66  fof(f1864,plain,(
% 2.02/0.66    ~r1_tarski(sK0,sK0) | spl4_164),
% 2.02/0.66    inference(avatar_component_clause,[],[f1862])).
% 2.02/0.66  fof(f165,plain,(
% 2.02/0.66    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 2.02/0.66    inference(resolution,[],[f106,f79])).
% 2.02/0.66  fof(f79,plain,(
% 2.02/0.66    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f23])).
% 2.02/0.66  fof(f23,axiom,(
% 2.02/0.66    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.02/0.66  fof(f106,plain,(
% 2.02/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.02/0.66    inference(cnf_transformation,[],[f54])).
% 2.02/0.66  fof(f54,plain,(
% 2.02/0.66    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.66    inference(ennf_transformation,[],[f19])).
% 2.02/0.66  fof(f19,axiom,(
% 2.02/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.02/0.66  fof(f115,plain,(
% 2.02/0.66    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.02/0.66    inference(definition_unfolding,[],[f76,f75])).
% 2.02/0.66  fof(f76,plain,(
% 2.02/0.66    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.02/0.66    inference(cnf_transformation,[],[f13])).
% 2.02/0.66  fof(f13,axiom,(
% 2.02/0.66    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.02/0.66  fof(f1752,plain,(
% 2.02/0.66    ~spl4_1 | spl4_160 | ~spl4_31 | ~spl4_125 | ~spl4_150),
% 2.02/0.66    inference(avatar_split_clause,[],[f1730,f1649,f1408,f569,f1749,f130])).
% 2.02/0.66  fof(f569,plain,(
% 2.02/0.66    spl4_31 <=> sK1 = k9_relat_1(sK2,k1_relat_1(sK2))),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 2.02/0.66  fof(f1649,plain,(
% 2.02/0.66    spl4_150 <=> k1_relat_1(sK3) = k9_relat_1(sK2,sK0)),
% 2.02/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).
% 2.02/0.66  fof(f1730,plain,(
% 2.02/0.66    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK3) | (~spl4_31 | ~spl4_125 | ~spl4_150)),
% 2.02/0.66    inference(superposition,[],[f118,f1724])).
% 2.02/0.66  fof(f1724,plain,(
% 2.02/0.66    sK1 = k1_relat_1(sK3) | (~spl4_31 | ~spl4_125 | ~spl4_150)),
% 2.02/0.66    inference(forward_demodulation,[],[f1651,f1541])).
% 2.02/0.66  fof(f1541,plain,(
% 2.02/0.66    sK1 = k9_relat_1(sK2,sK0) | (~spl4_31 | ~spl4_125)),
% 2.02/0.66    inference(superposition,[],[f571,f1490])).
% 2.02/0.66  fof(f571,plain,(
% 2.02/0.66    sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl4_31),
% 2.02/0.66    inference(avatar_component_clause,[],[f569])).
% 2.02/0.66  fof(f1651,plain,(
% 2.02/0.66    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~spl4_150),
% 2.02/0.66    inference(avatar_component_clause,[],[f1649])).
% 2.02/0.66  fof(f118,plain,(
% 2.02/0.66    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 2.02/0.66    inference(definition_unfolding,[],[f82,f75])).
% 2.02/0.66  fof(f82,plain,(
% 2.02/0.66    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.02/0.66    inference(cnf_transformation,[],[f31])).
% 2.02/0.66  fof(f31,plain,(
% 2.02/0.66    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.02/0.66    inference(ennf_transformation,[],[f10])).
% 2.02/0.66  fof(f10,axiom,(
% 2.02/0.66    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.02/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.02/0.66  fof(f1682,plain,(
% 2.02/0.66    ~spl4_1 | spl4_151),
% 2.02/0.66    inference(avatar_contradiction_clause,[],[f1680])).
% 2.02/0.66  fof(f1680,plain,(
% 2.02/0.66    $false | (~spl4_1 | spl4_151)),
% 2.02/0.66    inference(unit_resulting_resolution,[],[f132,f163,f1655,f99])).
% 2.02/0.66  fof(f1655,plain,(
% 2.02/0.66    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_151),
% 2.02/0.66    inference(avatar_component_clause,[],[f1653])).
% 2.02/0.68  fof(f1653,plain,(
% 2.02/0.68    spl4_151 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_151])])).
% 2.02/0.68  fof(f163,plain,(
% 2.02/0.68    v4_relat_1(sK3,sK1)),
% 2.02/0.68    inference(resolution,[],[f106,f65])).
% 2.02/0.68  fof(f65,plain,(
% 2.02/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f132,plain,(
% 2.02/0.68    v1_relat_1(sK3) | ~spl4_1),
% 2.02/0.68    inference(avatar_component_clause,[],[f130])).
% 2.02/0.68  fof(f1656,plain,(
% 2.02/0.68    ~spl4_1 | ~spl4_3 | ~spl4_8 | spl4_150 | ~spl4_151 | ~spl4_6 | ~spl4_109),
% 2.02/0.68    inference(avatar_split_clause,[],[f1647,f1181,f202,f1653,f1649,f265,f139,f130])).
% 2.02/0.68  fof(f1647,plain,(
% 2.02/0.68    ~r1_tarski(k1_relat_1(sK3),sK1) | k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl4_6 | ~spl4_109)),
% 2.02/0.68    inference(forward_demodulation,[],[f1646,f204])).
% 2.02/0.68  fof(f1646,plain,(
% 2.02/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,sK0) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_109),
% 2.02/0.68    inference(forward_demodulation,[],[f1593,f117])).
% 2.02/0.68  fof(f1593,plain,(
% 2.02/0.68    k1_relat_1(sK3) = k9_relat_1(sK2,k1_relat_1(k6_partfun1(sK0))) | ~v1_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~spl4_109),
% 2.02/0.68    inference(superposition,[],[f286,f1183])).
% 2.02/0.68  fof(f286,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 2.02/0.68    inference(duplicate_literal_removal,[],[f279])).
% 2.02/0.68  fof(f279,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k1_relat_1(X1) = k9_relat_1(X0,k1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X0) | ~r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(superposition,[],[f100,f83])).
% 2.02/0.68  fof(f83,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f32])).
% 2.02/0.68  fof(f32,plain,(
% 2.02/0.68    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.02/0.68    inference(ennf_transformation,[],[f6])).
% 2.02/0.68  fof(f6,axiom,(
% 2.02/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 2.02/0.68  fof(f100,plain,(
% 2.02/0.68    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f50])).
% 2.02/0.68  fof(f50,plain,(
% 2.02/0.68    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.02/0.68    inference(flattening,[],[f49])).
% 2.02/0.68  fof(f49,plain,(
% 2.02/0.68    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.02/0.68    inference(ennf_transformation,[],[f14])).
% 2.02/0.68  fof(f14,axiom,(
% 2.02/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 2.02/0.68  fof(f1441,plain,(
% 2.02/0.68    ~spl4_3 | spl4_126),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f1439])).
% 2.02/0.68  fof(f1439,plain,(
% 2.02/0.68    $false | (~spl4_3 | spl4_126)),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f141,f164,f1414,f99])).
% 2.02/0.68  fof(f1414,plain,(
% 2.02/0.68    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_126),
% 2.02/0.68    inference(avatar_component_clause,[],[f1412])).
% 2.02/0.68  fof(f1412,plain,(
% 2.02/0.68    spl4_126 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).
% 2.02/0.68  fof(f164,plain,(
% 2.02/0.68    v4_relat_1(sK2,sK0)),
% 2.02/0.68    inference(resolution,[],[f106,f74])).
% 2.02/0.68  fof(f74,plain,(
% 2.02/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f141,plain,(
% 2.02/0.68    v1_relat_1(sK2) | ~spl4_3),
% 2.02/0.68    inference(avatar_component_clause,[],[f139])).
% 2.02/0.68  fof(f1427,plain,(
% 2.02/0.68    ~spl4_92 | spl4_125 | ~spl4_126 | ~spl4_123),
% 2.02/0.68    inference(avatar_split_clause,[],[f1426,f1393,f1412,f1408,f1040])).
% 2.02/0.68  fof(f1040,plain,(
% 2.02/0.68    spl4_92 <=> v1_relat_1(k6_partfun1(k1_relat_1(sK2)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).
% 2.02/0.68  fof(f1393,plain,(
% 2.02/0.68    spl4_123 <=> k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_123])])).
% 2.02/0.68  fof(f1426,plain,(
% 2.02/0.68    ~r1_tarski(k1_relat_1(sK2),sK0) | k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~spl4_123),
% 2.02/0.68    inference(forward_demodulation,[],[f1403,f116])).
% 2.02/0.68  fof(f1403,plain,(
% 2.02/0.68    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~r1_tarski(k2_relat_1(k6_partfun1(k1_relat_1(sK2))),sK0) | ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~spl4_123),
% 2.02/0.68    inference(superposition,[],[f121,f1395])).
% 2.02/0.68  fof(f1395,plain,(
% 2.02/0.68    k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0)) | ~spl4_123),
% 2.02/0.68    inference(avatar_component_clause,[],[f1393])).
% 2.02/0.68  fof(f1396,plain,(
% 2.02/0.68    ~spl4_92 | ~spl4_1 | ~spl4_3 | spl4_123 | ~spl4_109),
% 2.02/0.68    inference(avatar_split_clause,[],[f1365,f1181,f1393,f139,f130,f1040])).
% 2.02/0.68  fof(f1365,plain,(
% 2.02/0.68    k6_partfun1(sK0) = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~spl4_109),
% 2.02/0.68    inference(superposition,[],[f316,f1183])).
% 2.02/0.68  fof(f316,plain,(
% 2.02/0.68    ( ! [X12,X11] : (k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12)) | ~v1_relat_1(X11) | ~v1_relat_1(X12) | ~v1_relat_1(k6_partfun1(k1_relat_1(X11)))) )),
% 2.02/0.68    inference(duplicate_literal_removal,[],[f307])).
% 2.02/0.68  fof(f307,plain,(
% 2.02/0.68    ( ! [X12,X11] : (k5_relat_1(X11,X12) = k5_relat_1(k6_partfun1(k1_relat_1(X11)),k5_relat_1(X11,X12)) | ~v1_relat_1(X11) | ~v1_relat_1(X12) | ~v1_relat_1(k6_partfun1(k1_relat_1(X11))) | ~v1_relat_1(X11)) )),
% 2.02/0.68    inference(superposition,[],[f84,f118])).
% 2.02/0.68  fof(f1233,plain,(
% 2.02/0.68    ~spl4_8 | ~spl4_45 | ~spl4_46 | ~spl4_5 | spl4_109 | ~spl4_107),
% 2.02/0.68    inference(avatar_split_clause,[],[f1229,f1172,f1181,f198,f695,f691,f265])).
% 2.02/0.68  fof(f691,plain,(
% 2.02/0.68    spl4_45 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.02/0.68  fof(f695,plain,(
% 2.02/0.68    spl4_46 <=> v1_funct_1(sK3)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.02/0.68  fof(f198,plain,(
% 2.02/0.68    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.02/0.68  fof(f1172,plain,(
% 2.02/0.68    spl4_107 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_107])])).
% 2.02/0.68  fof(f1229,plain,(
% 2.02/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_107),
% 2.02/0.68    inference(superposition,[],[f111,f1174])).
% 2.02/0.68  fof(f1174,plain,(
% 2.02/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_107),
% 2.02/0.68    inference(avatar_component_clause,[],[f1172])).
% 2.02/0.68  fof(f111,plain,(
% 2.02/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f60])).
% 2.02/0.68  fof(f60,plain,(
% 2.02/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.02/0.68    inference(flattening,[],[f59])).
% 2.02/0.68  fof(f59,plain,(
% 2.02/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.02/0.68    inference(ennf_transformation,[],[f24])).
% 2.02/0.68  fof(f24,axiom,(
% 2.02/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.02/0.68  fof(f1225,plain,(
% 2.02/0.68    spl4_106),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f1222])).
% 2.02/0.68  fof(f1222,plain,(
% 2.02/0.68    $false | spl4_106),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f72,f63,f65,f74,f1170,f113])).
% 2.02/0.68  fof(f113,plain,(
% 2.02/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f62])).
% 2.02/0.68  fof(f62,plain,(
% 2.02/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.02/0.68    inference(flattening,[],[f61])).
% 2.02/0.68  fof(f61,plain,(
% 2.02/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.02/0.68    inference(ennf_transformation,[],[f22])).
% 2.02/0.68  fof(f22,axiom,(
% 2.02/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.02/0.68  fof(f1170,plain,(
% 2.02/0.68    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_106),
% 2.02/0.68    inference(avatar_component_clause,[],[f1168])).
% 2.02/0.68  fof(f1168,plain,(
% 2.02/0.68    spl4_106 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 2.02/0.68  fof(f63,plain,(
% 2.02/0.68    v1_funct_1(sK3)),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f72,plain,(
% 2.02/0.68    v1_funct_1(sK2)),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f1175,plain,(
% 2.02/0.68    ~spl4_106 | spl4_107),
% 2.02/0.68    inference(avatar_split_clause,[],[f1164,f1172,f1168])).
% 2.02/0.68  fof(f1164,plain,(
% 2.02/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.02/0.68    inference(resolution,[],[f564,f67])).
% 2.02/0.68  fof(f67,plain,(
% 2.02/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f564,plain,(
% 2.02/0.68    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 2.02/0.68    inference(resolution,[],[f110,f79])).
% 2.02/0.68  fof(f110,plain,(
% 2.02/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f58])).
% 2.02/0.68  fof(f58,plain,(
% 2.02/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.68    inference(flattening,[],[f57])).
% 2.02/0.68  fof(f57,plain,(
% 2.02/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.02/0.68    inference(ennf_transformation,[],[f21])).
% 2.02/0.68  fof(f21,axiom,(
% 2.02/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.02/0.68  fof(f1053,plain,(
% 2.02/0.68    spl4_92),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f1049])).
% 2.02/0.68  fof(f1049,plain,(
% 2.02/0.68    $false | spl4_92),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f95,f79,f1042,f85])).
% 2.02/0.68  fof(f85,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f34])).
% 2.02/0.68  fof(f34,plain,(
% 2.02/0.68    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.02/0.68    inference(ennf_transformation,[],[f2])).
% 2.02/0.68  fof(f2,axiom,(
% 2.02/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.02/0.68  fof(f1042,plain,(
% 2.02/0.68    ~v1_relat_1(k6_partfun1(k1_relat_1(sK2))) | spl4_92),
% 2.02/0.68    inference(avatar_component_clause,[],[f1040])).
% 2.02/0.68  fof(f95,plain,(
% 2.02/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.02/0.68    inference(cnf_transformation,[],[f4])).
% 2.02/0.68  fof(f4,axiom,(
% 2.02/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.02/0.68  fof(f876,plain,(
% 2.02/0.68    ~spl4_3 | spl4_69),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f873])).
% 2.02/0.68  fof(f873,plain,(
% 2.02/0.68    $false | (~spl4_3 | spl4_69)),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f141,f68,f72,f871,f90])).
% 2.02/0.68  fof(f90,plain,(
% 2.02/0.68    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f40])).
% 2.02/0.68  fof(f40,plain,(
% 2.02/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.68    inference(flattening,[],[f39])).
% 2.02/0.68  fof(f39,plain,(
% 2.02/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.68    inference(ennf_transformation,[],[f16])).
% 2.02/0.68  fof(f16,axiom,(
% 2.02/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.02/0.68  fof(f871,plain,(
% 2.02/0.68    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl4_69),
% 2.02/0.68    inference(avatar_component_clause,[],[f869])).
% 2.02/0.68  fof(f68,plain,(
% 2.02/0.68    v2_funct_1(sK2)),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f712,plain,(
% 2.02/0.68    spl4_46),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f711])).
% 2.02/0.68  fof(f711,plain,(
% 2.02/0.68    $false | spl4_46),
% 2.02/0.68    inference(subsumption_resolution,[],[f63,f697])).
% 2.02/0.68  fof(f697,plain,(
% 2.02/0.68    ~v1_funct_1(sK3) | spl4_46),
% 2.02/0.68    inference(avatar_component_clause,[],[f695])).
% 2.02/0.68  fof(f710,plain,(
% 2.02/0.68    spl4_45),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f709])).
% 2.02/0.68  fof(f709,plain,(
% 2.02/0.68    $false | spl4_45),
% 2.02/0.68    inference(subsumption_resolution,[],[f65,f693])).
% 2.02/0.68  fof(f693,plain,(
% 2.02/0.68    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_45),
% 2.02/0.68    inference(avatar_component_clause,[],[f691])).
% 2.02/0.68  fof(f583,plain,(
% 2.02/0.68    spl4_32),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f578])).
% 2.02/0.68  fof(f578,plain,(
% 2.02/0.68    $false | spl4_32),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f115,f165,f575,f159])).
% 2.02/0.68  fof(f575,plain,(
% 2.02/0.68    ~r1_tarski(sK1,sK1) | spl4_32),
% 2.02/0.68    inference(avatar_component_clause,[],[f573])).
% 2.02/0.68  fof(f573,plain,(
% 2.02/0.68    spl4_32 <=> r1_tarski(sK1,sK1)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.02/0.68  fof(f576,plain,(
% 2.02/0.68    ~spl4_3 | ~spl4_8 | spl4_31 | ~spl4_32 | ~spl4_6 | ~spl4_27),
% 2.02/0.68    inference(avatar_split_clause,[],[f567,f532,f202,f573,f569,f265,f139])).
% 2.02/0.68  fof(f532,plain,(
% 2.02/0.68    spl4_27 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 2.02/0.68  fof(f567,plain,(
% 2.02/0.68    ~r1_tarski(sK1,sK1) | sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_6 | ~spl4_27)),
% 2.02/0.68    inference(forward_demodulation,[],[f566,f204])).
% 2.02/0.68  fof(f566,plain,(
% 2.02/0.68    sK1 = k9_relat_1(sK2,k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~r1_tarski(sK1,k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_27),
% 2.02/0.68    inference(superposition,[],[f100,f534])).
% 2.02/0.68  fof(f534,plain,(
% 2.02/0.68    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl4_27),
% 2.02/0.68    inference(avatar_component_clause,[],[f532])).
% 2.02/0.68  fof(f535,plain,(
% 2.02/0.68    ~spl4_7 | ~spl4_8 | ~spl4_3 | spl4_27 | ~spl4_14),
% 2.02/0.68    inference(avatar_split_clause,[],[f530,f426,f532,f139,f265,f261])).
% 2.02/0.68  fof(f426,plain,(
% 2.02/0.68    spl4_14 <=> ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(X0,sK1) | ~v1_relat_1(X0))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.02/0.68  fof(f530,plain,(
% 2.02/0.68    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_14),
% 2.02/0.68    inference(forward_demodulation,[],[f529,f117])).
% 2.02/0.68  fof(f529,plain,(
% 2.02/0.68    k10_relat_1(sK2,sK1) = k1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_14),
% 2.02/0.68    inference(duplicate_literal_removal,[],[f511])).
% 2.02/0.68  fof(f511,plain,(
% 2.02/0.68    k10_relat_1(sK2,sK1) = k1_relat_1(k6_partfun1(k1_relat_1(sK2))) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_14),
% 2.02/0.68    inference(superposition,[],[f427,f120])).
% 2.02/0.68  fof(f120,plain,(
% 2.02/0.68    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(definition_unfolding,[],[f91,f75])).
% 2.02/0.68  fof(f91,plain,(
% 2.02/0.68    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 2.02/0.68    inference(cnf_transformation,[],[f42])).
% 2.02/0.68  fof(f427,plain,(
% 2.02/0.68    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(X0,sK1) | ~v1_relat_1(X0)) ) | ~spl4_14),
% 2.02/0.68    inference(avatar_component_clause,[],[f426])).
% 2.02/0.68  fof(f428,plain,(
% 2.02/0.68    ~spl4_9 | spl4_14 | ~spl4_12),
% 2.02/0.68    inference(avatar_split_clause,[],[f416,f402,f426,f269])).
% 2.02/0.68  fof(f402,plain,(
% 2.02/0.68    spl4_12 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.02/0.68  fof(f416,plain,(
% 2.02/0.68    ( ! [X0] : (k1_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) = k10_relat_1(X0,sK1) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(X0)) ) | ~spl4_12),
% 2.02/0.68    inference(superposition,[],[f83,f404])).
% 2.02/0.68  fof(f404,plain,(
% 2.02/0.68    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_12),
% 2.02/0.68    inference(avatar_component_clause,[],[f402])).
% 2.02/0.68  fof(f405,plain,(
% 2.02/0.68    ~spl4_10 | ~spl4_9 | spl4_12 | ~spl4_11),
% 2.02/0.68    inference(avatar_split_clause,[],[f398,f385,f402,f269,f273])).
% 2.02/0.68  fof(f273,plain,(
% 2.02/0.68    spl4_10 <=> v4_relat_1(k2_funct_1(sK2),sK1)),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.02/0.68  fof(f385,plain,(
% 2.02/0.68    spl4_11 <=> r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2)))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.02/0.68  fof(f398,plain,(
% 2.02/0.68    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v4_relat_1(k2_funct_1(sK2),sK1) | ~spl4_11),
% 2.02/0.68    inference(resolution,[],[f387,f162])).
% 2.02/0.68  fof(f162,plain,(
% 2.02/0.68    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(X2)) | k1_relat_1(X2) = X1 | ~v1_relat_1(X2) | ~v4_relat_1(X2,X1)) )),
% 2.02/0.68    inference(resolution,[],[f104,f99])).
% 2.02/0.68  fof(f104,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.02/0.68    inference(cnf_transformation,[],[f1])).
% 2.02/0.68  fof(f1,axiom,(
% 2.02/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.02/0.68  fof(f387,plain,(
% 2.02/0.68    r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) | ~spl4_11),
% 2.02/0.68    inference(avatar_component_clause,[],[f385])).
% 2.02/0.68  fof(f388,plain,(
% 2.02/0.68    ~spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | spl4_11 | ~spl4_6),
% 2.02/0.68    inference(avatar_split_clause,[],[f378,f202,f385,f269,f265,f261,f139])).
% 2.02/0.68  fof(f378,plain,(
% 2.02/0.68    r1_tarski(sK1,k1_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_6),
% 2.02/0.68    inference(superposition,[],[f370,f204])).
% 2.02/0.68  fof(f370,plain,(
% 2.02/0.68    ( ! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1))) | ~v1_relat_1(k2_funct_1(X1)) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.02/0.68    inference(duplicate_literal_removal,[],[f367])).
% 2.02/0.68  fof(f367,plain,(
% 2.02/0.68    ( ! [X1] : (~v1_relat_1(k2_funct_1(X1)) | r1_tarski(k2_relat_1(X1),k1_relat_1(k2_funct_1(X1))) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X1))) )),
% 2.02/0.68    inference(resolution,[],[f187,f151])).
% 2.02/0.68  fof(f151,plain,(
% 2.02/0.68    ( ! [X0] : (v4_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(resolution,[],[f98,f122])).
% 2.02/0.68  fof(f122,plain,(
% 2.02/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/0.68    inference(equality_resolution,[],[f103])).
% 2.02/0.68  fof(f103,plain,(
% 2.02/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.02/0.68    inference(cnf_transformation,[],[f1])).
% 2.02/0.68  fof(f98,plain,(
% 2.02/0.68    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f48])).
% 2.02/0.68  fof(f187,plain,(
% 2.02/0.68    ( ! [X2,X1] : (~v4_relat_1(k2_funct_1(X1),X2) | ~v1_relat_1(k2_funct_1(X1)) | r1_tarski(k2_relat_1(X1),X2) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.02/0.68    inference(superposition,[],[f99,f89])).
% 2.02/0.68  fof(f89,plain,(
% 2.02/0.68    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f40])).
% 2.02/0.68  fof(f292,plain,(
% 2.02/0.68    ~spl4_3 | spl4_9),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f290])).
% 2.02/0.68  fof(f290,plain,(
% 2.02/0.68    $false | (~spl4_3 | spl4_9)),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f141,f72,f271,f86])).
% 2.02/0.68  fof(f86,plain,(
% 2.02/0.68    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.02/0.68    inference(cnf_transformation,[],[f36])).
% 2.02/0.68  fof(f36,plain,(
% 2.02/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.02/0.68    inference(flattening,[],[f35])).
% 2.02/0.68  fof(f35,plain,(
% 2.02/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.02/0.68    inference(ennf_transformation,[],[f12])).
% 2.02/0.68  fof(f12,axiom,(
% 2.02/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.02/0.68  fof(f271,plain,(
% 2.02/0.68    ~v1_relat_1(k2_funct_1(sK2)) | spl4_9),
% 2.02/0.68    inference(avatar_component_clause,[],[f269])).
% 2.02/0.68  fof(f289,plain,(
% 2.02/0.68    spl4_8),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f288])).
% 2.02/0.68  fof(f288,plain,(
% 2.02/0.68    $false | spl4_8),
% 2.02/0.68    inference(subsumption_resolution,[],[f72,f267])).
% 2.02/0.68  fof(f267,plain,(
% 2.02/0.68    ~v1_funct_1(sK2) | spl4_8),
% 2.02/0.68    inference(avatar_component_clause,[],[f265])).
% 2.02/0.68  fof(f278,plain,(
% 2.02/0.68    spl4_7),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f277])).
% 2.02/0.68  fof(f277,plain,(
% 2.02/0.68    $false | spl4_7),
% 2.02/0.68    inference(subsumption_resolution,[],[f68,f263])).
% 2.02/0.68  fof(f263,plain,(
% 2.02/0.68    ~v2_funct_1(sK2) | spl4_7),
% 2.02/0.68    inference(avatar_component_clause,[],[f261])).
% 2.02/0.68  fof(f276,plain,(
% 2.02/0.68    ~spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | spl4_10 | ~spl4_6),
% 2.02/0.68    inference(avatar_split_clause,[],[f258,f202,f273,f269,f265,f261,f139])).
% 2.02/0.68  fof(f258,plain,(
% 2.02/0.68    v4_relat_1(k2_funct_1(sK2),sK1) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_6),
% 2.02/0.68    inference(superposition,[],[f188,f204])).
% 2.02/0.68  fof(f188,plain,(
% 2.02/0.68    ( ! [X3] : (v4_relat_1(k2_funct_1(X3),k2_relat_1(X3)) | ~v1_relat_1(k2_funct_1(X3)) | ~v1_funct_1(X3) | ~v2_funct_1(X3) | ~v1_relat_1(X3)) )),
% 2.02/0.68    inference(superposition,[],[f151,f89])).
% 2.02/0.68  fof(f208,plain,(
% 2.02/0.68    spl4_5),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f207])).
% 2.02/0.68  fof(f207,plain,(
% 2.02/0.68    $false | spl4_5),
% 2.02/0.68    inference(subsumption_resolution,[],[f74,f200])).
% 2.02/0.68  fof(f200,plain,(
% 2.02/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 2.02/0.68    inference(avatar_component_clause,[],[f198])).
% 2.02/0.68  fof(f206,plain,(
% 2.02/0.68    ~spl4_5 | spl4_6),
% 2.02/0.68    inference(avatar_split_clause,[],[f196,f202,f198])).
% 2.02/0.68  fof(f196,plain,(
% 2.02/0.68    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.02/0.68    inference(superposition,[],[f66,f105])).
% 2.02/0.68  fof(f105,plain,(
% 2.02/0.68    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.02/0.68    inference(cnf_transformation,[],[f53])).
% 2.02/0.68  fof(f53,plain,(
% 2.02/0.68    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.02/0.68    inference(ennf_transformation,[],[f20])).
% 2.02/0.68  fof(f20,axiom,(
% 2.02/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.02/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.02/0.68  fof(f66,plain,(
% 2.02/0.68    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.02/0.68    inference(cnf_transformation,[],[f30])).
% 2.02/0.68  fof(f156,plain,(
% 2.02/0.68    spl4_4),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f153])).
% 2.02/0.68  fof(f153,plain,(
% 2.02/0.68    $false | spl4_4),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f95,f145])).
% 2.02/0.68  fof(f145,plain,(
% 2.02/0.68    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 2.02/0.68    inference(avatar_component_clause,[],[f143])).
% 2.02/0.68  fof(f143,plain,(
% 2.02/0.68    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 2.02/0.68  fof(f150,plain,(
% 2.02/0.68    spl4_2),
% 2.02/0.68    inference(avatar_contradiction_clause,[],[f147])).
% 2.02/0.68  fof(f147,plain,(
% 2.02/0.68    $false | spl4_2),
% 2.02/0.68    inference(unit_resulting_resolution,[],[f95,f136])).
% 2.02/0.68  fof(f136,plain,(
% 2.02/0.68    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 2.02/0.68    inference(avatar_component_clause,[],[f134])).
% 2.02/0.68  fof(f134,plain,(
% 2.02/0.68    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.02/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.02/0.68  fof(f146,plain,(
% 2.02/0.68    spl4_3 | ~spl4_4),
% 2.02/0.68    inference(avatar_split_clause,[],[f127,f143,f139])).
% 2.02/0.68  fof(f127,plain,(
% 2.02/0.68    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 2.02/0.68    inference(resolution,[],[f85,f74])).
% 2.02/0.68  fof(f137,plain,(
% 2.02/0.68    spl4_1 | ~spl4_2),
% 2.02/0.68    inference(avatar_split_clause,[],[f126,f134,f130])).
% 2.02/0.68  fof(f126,plain,(
% 2.02/0.68    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 2.02/0.68    inference(resolution,[],[f85,f65])).
% 2.02/0.68  % SZS output end Proof for theBenchmark
% 2.02/0.68  % (5995)------------------------------
% 2.02/0.68  % (5995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.68  % (5995)Termination reason: Refutation
% 2.02/0.68  
% 2.02/0.68  % (5995)Memory used [KB]: 7931
% 2.02/0.68  % (5995)Time elapsed: 0.257 s
% 2.02/0.68  % (5995)------------------------------
% 2.02/0.68  % (5995)------------------------------
% 2.02/0.68  % (5978)Success in time 0.323 s
%------------------------------------------------------------------------------
