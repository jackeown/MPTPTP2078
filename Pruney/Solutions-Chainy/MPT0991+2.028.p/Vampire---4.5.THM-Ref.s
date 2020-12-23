%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:08 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 463 expanded)
%              Number of leaves         :   41 ( 166 expanded)
%              Depth                    :   11
%              Number of atoms          :  695 (1818 expanded)
%              Number of equality atoms :  117 ( 379 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2753,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f153,f185,f213,f215,f223,f232,f244,f248,f278,f316,f318,f336,f345,f350,f443,f447,f481,f490,f526,f527,f562,f624,f804,f812,f839,f1108,f1948,f2414,f2752])).

fof(f2752,plain,
    ( ~ spl4_19
    | ~ spl4_16
    | spl4_32
    | ~ spl4_58
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_63 ),
    inference(avatar_split_clause,[],[f2751,f1946,f321,f238,f170,f135,f1094,f436,f241,f298])).

fof(f298,plain,
    ( spl4_19
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f241,plain,
    ( spl4_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f436,plain,
    ( spl4_32
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f1094,plain,
    ( spl4_58
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f135,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f170,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f238,plain,
    ( spl4_15
  <=> ! [X3] : v1_funct_2(sK2,k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f321,plain,
    ( spl4_23
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1946,plain,
    ( spl4_63
  <=> ! [X3] :
        ( v2_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_funct_1(k5_relat_1(X3,k1_xboole_0))
        | ~ v1_funct_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f2751,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_23
    | ~ spl4_63 ),
    inference(forward_demodulation,[],[f2750,f556])).

fof(f556,plain,
    ( k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f555,f58])).

fof(f58,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f37,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f36,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f555,plain,
    ( k6_partfun1(k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f538,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f538,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k1_xboole_0)
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(superposition,[],[f323,f172])).

fof(f172,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f323,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f321])).

fof(f2750,plain,
    ( v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v2_funct_1(k5_relat_1(sK2,k1_xboole_0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_15
    | ~ spl4_63 ),
    inference(resolution,[],[f1947,f239])).

fof(f239,plain,
    ( ! [X3] : v1_funct_2(sK2,k1_xboole_0,X3)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f238])).

fof(f1947,plain,
    ( ! [X3] :
        ( ~ v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0))
        | v2_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v2_funct_1(k5_relat_1(X3,k1_xboole_0))
        | ~ v1_funct_1(X3) )
    | ~ spl4_63 ),
    inference(avatar_component_clause,[],[f1946])).

fof(f2414,plain,(
    ~ spl4_62 ),
    inference(avatar_contradiction_clause,[],[f1965])).

fof(f1965,plain,
    ( $false
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f34,f1944])).

fof(f1944,plain,
    ( ! [X4] : k1_xboole_0 = X4
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f1943])).

fof(f1943,plain,
    ( spl4_62
  <=> ! [X4] : k1_xboole_0 = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f34,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

fof(f1948,plain,
    ( spl4_62
    | spl4_63
    | ~ spl4_46
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f1941,f837,f810,f1946,f1943])).

fof(f810,plain,
    ( spl4_46
  <=> ! [X3,X2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f837,plain,
    ( spl4_48
  <=> ! [X13,X15,X12,X14] :
        ( ~ v1_funct_2(X12,X13,X14)
        | v2_funct_1(X12)
        | k1_xboole_0 = X15
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(k5_relat_1(X12,k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,X14,X15)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f1941,plain,
    ( ! [X4,X3] :
        ( v2_funct_1(X3)
        | k1_xboole_0 = X4
        | ~ v1_funct_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,k1_xboole_0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0)) )
    | ~ spl4_46
    | ~ spl4_48 ),
    inference(duplicate_literal_removal,[],[f1940])).

fof(f1940,plain,
    ( ! [X4,X3] :
        ( v2_funct_1(X3)
        | k1_xboole_0 = X4
        | ~ v1_funct_1(X3)
        | ~ v2_funct_1(k5_relat_1(X3,k1_xboole_0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0))
        | k1_xboole_0 = X4 )
    | ~ spl4_46
    | ~ spl4_48 ),
    inference(resolution,[],[f1087,f826])).

fof(f826,plain,
    ( ! [X16] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X16)
        | k1_xboole_0 = X16 )
    | ~ spl4_46 ),
    inference(resolution,[],[f811,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | k1_xboole_0 = X0
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f49,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

% (11068)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
fof(f811,plain,
    ( ! [X2,X3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f810])).

fof(f1087,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_2(k1_xboole_0,X3,X5)
        | v2_funct_1(X4)
        | k1_xboole_0 = X5
        | ~ v1_funct_1(X4)
        | ~ v2_funct_1(k5_relat_1(X4,k1_xboole_0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X4,k1_xboole_0,X3) )
    | ~ spl4_48 ),
    inference(superposition,[],[f838,f63])).

fof(f63,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f838,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | v2_funct_1(X12)
        | k1_xboole_0 = X15
        | ~ v1_funct_1(X12)
        | ~ v2_funct_1(k5_relat_1(X12,k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,X14,X15)
        | ~ v1_funct_2(X12,X13,X14) )
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f837])).

fof(f1108,plain,(
    spl4_58 ),
    inference(avatar_contradiction_clause,[],[f1107])).

fof(f1107,plain,
    ( $false
    | spl4_58 ),
    inference(subsumption_resolution,[],[f73,f1096])).

fof(f1096,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_58 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f73,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f60,f58])).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f839,plain,
    ( ~ spl4_29
    | spl4_48
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f825,f810,f837,f403])).

fof(f403,plain,
    ( spl4_29
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f825,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ v1_funct_2(X12,X13,X14)
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,X14,X15)
        | ~ v2_funct_1(k5_relat_1(X12,k1_xboole_0))
        | ~ v1_funct_1(X12)
        | k1_xboole_0 = X15
        | v2_funct_1(X12) )
    | ~ spl4_46 ),
    inference(resolution,[],[f811,f434])).

fof(f434,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v2_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f432])).

fof(f432,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k5_relat_1(X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3) ) ),
    inference(superposition,[],[f51,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f812,plain,
    ( spl4_46
    | ~ spl4_2
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f807,f802,f93,f810])).

fof(f93,plain,
    ( spl4_2
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f802,plain,
    ( spl4_45
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f807,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) )
    | ~ spl4_45 ),
    inference(superposition,[],[f803,f63])).

fof(f803,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f802])).

fof(f804,plain,
    ( spl4_45
    | ~ spl4_16
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f797,f589,f241,f802])).

fof(f589,plain,
    ( spl4_36
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f797,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
    | ~ spl4_36 ),
    inference(superposition,[],[f590,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f590,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f589])).

fof(f624,plain,
    ( ~ spl4_19
    | ~ spl4_29
    | spl4_36
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f623,f321,f170,f135,f589,f403,f298])).

fof(f623,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_1(k1_xboole_0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(superposition,[],[f335,f556])).

fof(f335,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f332])).

fof(f332,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f57,f55])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f562,plain,
    ( ~ spl4_5
    | spl4_16 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | ~ spl4_5
    | spl4_16 ),
    inference(subsumption_resolution,[],[f509,f243])).

fof(f243,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f241])).

fof(f509,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f495,f63])).

fof(f495,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5 ),
    inference(superposition,[],[f33,f137])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f527,plain,
    ( ~ spl4_9
    | spl4_10
    | spl4_8
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f520,f135,f148,f170,f166])).

fof(f166,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f148,plain,
    ( spl4_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f520,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(resolution,[],[f491,f113])).

fof(f113,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f491,plain,
    ( v1_funct_2(sK3,sK1,k1_xboole_0)
    | ~ spl4_5 ),
    inference(superposition,[],[f28,f137])).

fof(f28,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f526,plain,
    ( ~ spl4_5
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f523])).

fof(f523,plain,
    ( $false
    | ~ spl4_5
    | spl4_9 ),
    inference(subsumption_resolution,[],[f168,f507])).

fof(f507,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f492,f62])).

fof(f492,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f29,f137])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f168,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f490,plain,(
    ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f35,f438])).

fof(f438,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f436])).

fof(f35,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f481,plain,
    ( ~ spl4_5
    | ~ spl4_24
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f480])).

fof(f480,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_24
    | spl4_29 ),
    inference(subsumption_resolution,[],[f405,f479])).

fof(f479,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl4_5
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f463,f58])).

fof(f463,plain,
    ( v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_24 ),
    inference(superposition,[],[f349,f137])).

fof(f349,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl4_24
  <=> v1_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f405,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f403])).

fof(f447,plain,(
    spl4_33 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | spl4_33 ),
    inference(unit_resulting_resolution,[],[f60,f442])).

fof(f442,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_33 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl4_33
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f443,plain,
    ( spl4_32
    | spl4_5
    | ~ spl4_19
    | ~ spl4_11
    | ~ spl4_3
    | ~ spl4_20
    | ~ spl4_13
    | ~ spl4_6
    | ~ spl4_33
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f433,f275,f440,f140,f205,f302,f127,f191,f298,f135,f436])).

fof(f191,plain,
    ( spl4_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f127,plain,
    ( spl4_3
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f302,plain,
    ( spl4_20
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f205,plain,
    ( spl4_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f140,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f275,plain,
    ( spl4_18
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f433,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f51,f277])).

fof(f277,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f275])).

fof(f350,plain,
    ( ~ spl4_19
    | ~ spl4_11
    | ~ spl4_20
    | ~ spl4_13
    | spl4_24
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f343,f275,f347,f205,f302,f191,f298])).

fof(f343,plain,
    ( v1_funct_1(k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f56,f277])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f345,plain,
    ( ~ spl4_19
    | ~ spl4_11
    | ~ spl4_20
    | ~ spl4_13
    | spl4_23
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f342,f275,f321,f205,f302,f191,f298])).

fof(f342,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f55,f277])).

fof(f336,plain,(
    spl4_17 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f31,f27,f29,f33,f273,f57])).

fof(f273,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl4_17
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f318,plain,(
    spl4_20 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl4_20 ),
    inference(subsumption_resolution,[],[f27,f304])).

fof(f304,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_20 ),
    inference(avatar_component_clause,[],[f302])).

fof(f316,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f31,f300])).

fof(f300,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f298])).

fof(f278,plain,
    ( ~ spl4_17
    | spl4_18 ),
    inference(avatar_split_clause,[],[f268,f275,f271])).

fof(f268,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f181,f30])).

fof(f30,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f54,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f248,plain,
    ( ~ spl4_6
    | spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f246,f148,f144,f140])).

fof(f144,plain,
    ( spl4_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f246,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f244,plain,
    ( spl4_15
    | ~ spl4_16
    | ~ spl4_5
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f236,f209,f135,f241,f238])).

fof(f209,plain,
    ( spl4_14
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f236,plain,
    ( ! [X3] :
        ( k1_xboole_0 != sK0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(sK2,k1_xboole_0,X3) )
    | ~ spl4_14 ),
    inference(superposition,[],[f112,f211])).

fof(f211,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f209])).

fof(f112,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f109,f63])).

fof(f109,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X3,k1_xboole_0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f107,f44])).

fof(f107,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f65,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f232,plain,(
    ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f34,f150])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f223,plain,(
    spl4_13 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl4_13 ),
    inference(subsumption_resolution,[],[f33,f207])).

fof(f207,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f215,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f29,f193])).

fof(f193,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f213,plain,
    ( ~ spl4_13
    | spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f202,f144,f209,f205])).

fof(f202,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(superposition,[],[f44,f146])).

fof(f146,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f185,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f32,f142])).

fof(f142,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f153,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f28,f129])).

fof(f129,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f98,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl4_2 ),
    inference(subsumption_resolution,[],[f77,f95])).

fof(f95,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f77,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f74,f62])).

fof(f74,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f59,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (11038)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (11034)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (11036)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (11054)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (11045)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (11048)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (11056)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (11046)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (11042)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (11048)Refutation not found, incomplete strategy% (11048)------------------------------
% 0.20/0.53  % (11048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11035)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (11048)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11048)Memory used [KB]: 10746
% 0.20/0.53  % (11048)Time elapsed: 0.118 s
% 0.20/0.53  % (11048)------------------------------
% 0.20/0.53  % (11048)------------------------------
% 0.20/0.53  % (11033)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (11040)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.54  % (11037)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (11039)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (11047)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (11044)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (11056)Refutation not found, incomplete strategy% (11056)------------------------------
% 0.20/0.54  % (11056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (11056)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (11056)Memory used [KB]: 10746
% 0.20/0.54  % (11056)Time elapsed: 0.120 s
% 0.20/0.54  % (11056)------------------------------
% 0.20/0.54  % (11056)------------------------------
% 0.20/0.54  % (11050)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (11032)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (11061)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (11051)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (11060)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.55  % (11049)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (11059)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (11058)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (11057)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (11053)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (11052)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.56  % (11055)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.56  % (11041)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % (11043)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.56  % (11042)Refutation not found, incomplete strategy% (11042)------------------------------
% 0.20/0.56  % (11042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11060)Refutation not found, incomplete strategy% (11060)------------------------------
% 0.20/0.57  % (11060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11060)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (11060)Memory used [KB]: 10874
% 0.20/0.57  % (11060)Time elapsed: 0.140 s
% 0.20/0.57  % (11060)------------------------------
% 0.20/0.57  % (11060)------------------------------
% 0.20/0.57  % (11042)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (11042)Memory used [KB]: 10874
% 0.20/0.57  % (11042)Time elapsed: 0.143 s
% 0.20/0.57  % (11042)------------------------------
% 0.20/0.57  % (11042)------------------------------
% 0.20/0.57  % (11059)Refutation not found, incomplete strategy% (11059)------------------------------
% 0.20/0.57  % (11059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (11059)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (11059)Memory used [KB]: 6268
% 0.20/0.57  % (11059)Time elapsed: 0.138 s
% 0.20/0.57  % (11059)------------------------------
% 0.20/0.57  % (11059)------------------------------
% 0.20/0.59  % (11055)Refutation not found, incomplete strategy% (11055)------------------------------
% 0.20/0.59  % (11055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (11055)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (11055)Memory used [KB]: 11129
% 0.20/0.59  % (11055)Time elapsed: 0.135 s
% 0.20/0.59  % (11055)------------------------------
% 0.20/0.59  % (11055)------------------------------
% 2.11/0.65  % (11067)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.11/0.66  % (11045)Refutation found. Thanks to Tanya!
% 2.11/0.66  % SZS status Theorem for theBenchmark
% 2.11/0.66  % SZS output start Proof for theBenchmark
% 2.11/0.66  fof(f2753,plain,(
% 2.11/0.66    $false),
% 2.11/0.66    inference(avatar_sat_refutation,[],[f98,f153,f185,f213,f215,f223,f232,f244,f248,f278,f316,f318,f336,f345,f350,f443,f447,f481,f490,f526,f527,f562,f624,f804,f812,f839,f1108,f1948,f2414,f2752])).
% 2.11/0.66  fof(f2752,plain,(
% 2.11/0.66    ~spl4_19 | ~spl4_16 | spl4_32 | ~spl4_58 | ~spl4_5 | ~spl4_10 | ~spl4_15 | ~spl4_23 | ~spl4_63),
% 2.11/0.66    inference(avatar_split_clause,[],[f2751,f1946,f321,f238,f170,f135,f1094,f436,f241,f298])).
% 2.11/0.66  fof(f298,plain,(
% 2.11/0.66    spl4_19 <=> v1_funct_1(sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 2.11/0.66  fof(f241,plain,(
% 2.11/0.66    spl4_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 2.11/0.66  fof(f436,plain,(
% 2.11/0.66    spl4_32 <=> v2_funct_1(sK2)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 2.11/0.66  fof(f1094,plain,(
% 2.11/0.66    spl4_58 <=> v2_funct_1(k1_xboole_0)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 2.11/0.66  fof(f135,plain,(
% 2.11/0.66    spl4_5 <=> k1_xboole_0 = sK0),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.11/0.66  fof(f170,plain,(
% 2.11/0.66    spl4_10 <=> k1_xboole_0 = sK3),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 2.11/0.66  fof(f238,plain,(
% 2.11/0.66    spl4_15 <=> ! [X3] : v1_funct_2(sK2,k1_xboole_0,X3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.11/0.66  fof(f321,plain,(
% 2.11/0.66    spl4_23 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 2.11/0.66  fof(f1946,plain,(
% 2.11/0.66    spl4_63 <=> ! [X3] : (v2_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v2_funct_1(k5_relat_1(X3,k1_xboole_0)) | ~v1_funct_1(X3))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 2.11/0.66  fof(f2751,plain,(
% 2.11/0.66    ~v2_funct_1(k1_xboole_0) | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(sK2) | (~spl4_5 | ~spl4_10 | ~spl4_15 | ~spl4_23 | ~spl4_63)),
% 2.11/0.66    inference(forward_demodulation,[],[f2750,f556])).
% 2.11/0.66  fof(f556,plain,(
% 2.11/0.66    k1_xboole_0 = k5_relat_1(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_10 | ~spl4_23)),
% 2.11/0.66    inference(forward_demodulation,[],[f555,f58])).
% 2.11/0.66  fof(f58,plain,(
% 2.11/0.66    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.11/0.66    inference(definition_unfolding,[],[f36,f37])).
% 2.11/0.66  fof(f37,plain,(
% 2.11/0.66    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f10])).
% 2.11/0.66  fof(f10,axiom,(
% 2.11/0.66    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.11/0.66  fof(f36,plain,(
% 2.11/0.66    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.11/0.66    inference(cnf_transformation,[],[f2])).
% 2.11/0.66  fof(f2,axiom,(
% 2.11/0.66    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 2.11/0.66  fof(f555,plain,(
% 2.11/0.66    k6_partfun1(k1_xboole_0) = k5_relat_1(sK2,k1_xboole_0) | (~spl4_5 | ~spl4_10 | ~spl4_23)),
% 2.11/0.66    inference(forward_demodulation,[],[f538,f137])).
% 2.11/0.66  fof(f137,plain,(
% 2.11/0.66    k1_xboole_0 = sK0 | ~spl4_5),
% 2.11/0.66    inference(avatar_component_clause,[],[f135])).
% 2.11/0.66  fof(f538,plain,(
% 2.11/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,k1_xboole_0) | (~spl4_10 | ~spl4_23)),
% 2.11/0.66    inference(superposition,[],[f323,f172])).
% 2.11/0.66  fof(f172,plain,(
% 2.11/0.66    k1_xboole_0 = sK3 | ~spl4_10),
% 2.11/0.66    inference(avatar_component_clause,[],[f170])).
% 2.11/0.66  fof(f323,plain,(
% 2.11/0.66    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_23),
% 2.11/0.66    inference(avatar_component_clause,[],[f321])).
% 2.11/0.66  fof(f2750,plain,(
% 2.11/0.66    v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v2_funct_1(k5_relat_1(sK2,k1_xboole_0)) | ~v1_funct_1(sK2) | (~spl4_15 | ~spl4_63)),
% 2.11/0.66    inference(resolution,[],[f1947,f239])).
% 2.11/0.66  fof(f239,plain,(
% 2.11/0.66    ( ! [X3] : (v1_funct_2(sK2,k1_xboole_0,X3)) ) | ~spl4_15),
% 2.11/0.66    inference(avatar_component_clause,[],[f238])).
% 2.11/0.66  fof(f1947,plain,(
% 2.11/0.66    ( ! [X3] : (~v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0)) | v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v2_funct_1(k5_relat_1(X3,k1_xboole_0)) | ~v1_funct_1(X3)) ) | ~spl4_63),
% 2.11/0.66    inference(avatar_component_clause,[],[f1946])).
% 2.11/0.66  fof(f2414,plain,(
% 2.11/0.66    ~spl4_62),
% 2.11/0.66    inference(avatar_contradiction_clause,[],[f1965])).
% 2.11/0.66  fof(f1965,plain,(
% 2.11/0.66    $false | ~spl4_62),
% 2.11/0.66    inference(subsumption_resolution,[],[f34,f1944])).
% 2.11/0.66  fof(f1944,plain,(
% 2.11/0.66    ( ! [X4] : (k1_xboole_0 = X4) ) | ~spl4_62),
% 2.11/0.66    inference(avatar_component_clause,[],[f1943])).
% 2.11/0.66  fof(f1943,plain,(
% 2.11/0.66    spl4_62 <=> ! [X4] : k1_xboole_0 = X4),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 2.11/0.66  fof(f34,plain,(
% 2.11/0.66    k1_xboole_0 != sK1),
% 2.11/0.66    inference(cnf_transformation,[],[f15])).
% 2.11/0.66  fof(f15,plain,(
% 2.11/0.66    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.11/0.66    inference(flattening,[],[f14])).
% 2.11/0.66  fof(f14,plain,(
% 2.11/0.66    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.11/0.66    inference(ennf_transformation,[],[f13])).
% 2.11/0.66  fof(f13,negated_conjecture,(
% 2.11/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 2.11/0.66    inference(negated_conjecture,[],[f12])).
% 2.11/0.66  fof(f12,conjecture,(
% 2.11/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).
% 2.11/0.66  fof(f1948,plain,(
% 2.11/0.66    spl4_62 | spl4_63 | ~spl4_46 | ~spl4_48),
% 2.11/0.66    inference(avatar_split_clause,[],[f1941,f837,f810,f1946,f1943])).
% 2.11/0.66  fof(f810,plain,(
% 2.11/0.66    spl4_46 <=> ! [X3,X2] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 2.11/0.66  fof(f837,plain,(
% 2.11/0.66    spl4_48 <=> ! [X13,X15,X12,X14] : (~v1_funct_2(X12,X13,X14) | v2_funct_1(X12) | k1_xboole_0 = X15 | ~v1_funct_1(X12) | ~v2_funct_1(k5_relat_1(X12,k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,X14,X15) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))))),
% 2.11/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 2.11/0.66  fof(f1941,plain,(
% 2.11/0.66    ( ! [X4,X3] : (v2_funct_1(X3) | k1_xboole_0 = X4 | ~v1_funct_1(X3) | ~v2_funct_1(k5_relat_1(X3,k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0))) ) | (~spl4_46 | ~spl4_48)),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f1940])).
% 2.11/0.66  fof(f1940,plain,(
% 2.11/0.66    ( ! [X4,X3] : (v2_funct_1(X3) | k1_xboole_0 = X4 | ~v1_funct_1(X3) | ~v2_funct_1(k5_relat_1(X3,k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,k1_relat_1(k1_xboole_0)) | k1_xboole_0 = X4) ) | (~spl4_46 | ~spl4_48)),
% 2.11/0.66    inference(resolution,[],[f1087,f826])).
% 2.11/0.66  fof(f826,plain,(
% 2.11/0.66    ( ! [X16] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X16) | k1_xboole_0 = X16) ) | ~spl4_46),
% 2.11/0.66    inference(resolution,[],[f811,f119])).
% 2.11/0.66  fof(f119,plain,(
% 2.11/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | k1_xboole_0 = X0 | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 2.11/0.66    inference(equality_resolution,[],[f118])).
% 2.11/0.66  fof(f118,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 2.11/0.66    inference(duplicate_literal_removal,[],[f116])).
% 2.11/0.66  fof(f116,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k1_relat_1(X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/0.66    inference(superposition,[],[f49,f44])).
% 2.11/0.66  fof(f44,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.11/0.66    inference(cnf_transformation,[],[f16])).
% 2.11/0.66  fof(f16,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.66    inference(ennf_transformation,[],[f4])).
% 2.11/0.66  fof(f4,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.11/0.66  fof(f49,plain,(
% 2.11/0.66    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(X2,X0,X1)) )),
% 2.11/0.66    inference(cnf_transformation,[],[f18])).
% 2.11/0.66  fof(f18,plain,(
% 2.11/0.66    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.66    inference(flattening,[],[f17])).
% 2.11/0.66  fof(f17,plain,(
% 2.11/0.66    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.66    inference(ennf_transformation,[],[f7])).
% 2.11/0.66  fof(f7,axiom,(
% 2.11/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.11/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 2.11/0.67  % (11068)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.11/0.68  fof(f811,plain,(
% 2.11/0.68    ( ! [X2,X3] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))) ) | ~spl4_46),
% 2.11/0.68    inference(avatar_component_clause,[],[f810])).
% 2.11/0.68  fof(f1087,plain,(
% 2.11/0.68    ( ! [X4,X5,X3] : (~v1_funct_2(k1_xboole_0,X3,X5) | v2_funct_1(X4) | k1_xboole_0 = X5 | ~v1_funct_1(X4) | ~v2_funct_1(k5_relat_1(X4,k1_xboole_0)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X4,k1_xboole_0,X3)) ) | ~spl4_48),
% 2.11/0.68    inference(superposition,[],[f838,f63])).
% 2.11/0.68  fof(f63,plain,(
% 2.11/0.68    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.11/0.68    inference(equality_resolution,[],[f42])).
% 2.11/0.68  fof(f42,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 2.11/0.68    inference(cnf_transformation,[],[f1])).
% 2.11/0.68  fof(f1,axiom,(
% 2.11/0.68    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.11/0.68  fof(f838,plain,(
% 2.11/0.68    ( ! [X14,X12,X15,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | v2_funct_1(X12) | k1_xboole_0 = X15 | ~v1_funct_1(X12) | ~v2_funct_1(k5_relat_1(X12,k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,X14,X15) | ~v1_funct_2(X12,X13,X14)) ) | ~spl4_48),
% 2.11/0.68    inference(avatar_component_clause,[],[f837])).
% 2.11/0.68  fof(f1108,plain,(
% 2.11/0.68    spl4_58),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f1107])).
% 2.11/0.68  fof(f1107,plain,(
% 2.11/0.68    $false | spl4_58),
% 2.11/0.68    inference(subsumption_resolution,[],[f73,f1096])).
% 2.11/0.68  fof(f1096,plain,(
% 2.11/0.68    ~v2_funct_1(k1_xboole_0) | spl4_58),
% 2.11/0.68    inference(avatar_component_clause,[],[f1094])).
% 2.11/0.68  fof(f73,plain,(
% 2.11/0.68    v2_funct_1(k1_xboole_0)),
% 2.11/0.68    inference(superposition,[],[f60,f58])).
% 2.11/0.68  fof(f60,plain,(
% 2.11/0.68    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.11/0.68    inference(definition_unfolding,[],[f40,f37])).
% 2.11/0.68  fof(f40,plain,(
% 2.11/0.68    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.11/0.68    inference(cnf_transformation,[],[f3])).
% 2.11/0.68  fof(f3,axiom,(
% 2.11/0.68    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.11/0.68  fof(f839,plain,(
% 2.11/0.68    ~spl4_29 | spl4_48 | ~spl4_46),
% 2.11/0.68    inference(avatar_split_clause,[],[f825,f810,f837,f403])).
% 2.11/0.68  fof(f403,plain,(
% 2.11/0.68    spl4_29 <=> v1_funct_1(k1_xboole_0)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 2.11/0.68  fof(f825,plain,(
% 2.11/0.68    ( ! [X14,X12,X15,X13] : (~v1_funct_2(X12,X13,X14) | ~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,X14,X15) | ~v2_funct_1(k5_relat_1(X12,k1_xboole_0)) | ~v1_funct_1(X12) | k1_xboole_0 = X15 | v2_funct_1(X12)) ) | ~spl4_46),
% 2.11/0.68    inference(resolution,[],[f811,f434])).
% 2.11/0.68  fof(f434,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~v2_funct_1(k5_relat_1(X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f432])).
% 2.11/0.68  fof(f432,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k5_relat_1(X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3)) )),
% 2.11/0.68    inference(superposition,[],[f51,f55])).
% 2.11/0.68  fof(f55,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f24])).
% 2.11/0.68  fof(f24,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.11/0.68    inference(flattening,[],[f23])).
% 2.11/0.68  fof(f23,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.11/0.68    inference(ennf_transformation,[],[f9])).
% 2.11/0.68  fof(f9,axiom,(
% 2.11/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.11/0.68  fof(f51,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f20])).
% 2.11/0.68  fof(f20,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.11/0.68    inference(flattening,[],[f19])).
% 2.11/0.68  fof(f19,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.11/0.68    inference(ennf_transformation,[],[f11])).
% 2.11/0.68  fof(f11,axiom,(
% 2.11/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 2.11/0.68  fof(f812,plain,(
% 2.11/0.68    spl4_46 | ~spl4_2 | ~spl4_45),
% 2.11/0.68    inference(avatar_split_clause,[],[f807,f802,f93,f810])).
% 2.11/0.68  fof(f93,plain,(
% 2.11/0.68    spl4_2 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.11/0.68  fof(f802,plain,(
% 2.11/0.68    spl4_45 <=> ! [X1,X0,X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 2.11/0.68  fof(f807,plain,(
% 2.11/0.68    ( ! [X2,X3] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))) ) | ~spl4_45),
% 2.11/0.68    inference(superposition,[],[f803,f63])).
% 2.11/0.68  fof(f803,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl4_45),
% 2.11/0.68    inference(avatar_component_clause,[],[f802])).
% 2.11/0.68  fof(f804,plain,(
% 2.11/0.68    spl4_45 | ~spl4_16 | ~spl4_36),
% 2.11/0.68    inference(avatar_split_clause,[],[f797,f589,f241,f802])).
% 2.11/0.68  fof(f589,plain,(
% 2.11/0.68    spl4_36 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 2.11/0.68  fof(f797,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) ) | ~spl4_36),
% 2.11/0.68    inference(superposition,[],[f590,f62])).
% 2.11/0.68  fof(f62,plain,(
% 2.11/0.68    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.11/0.68    inference(equality_resolution,[],[f43])).
% 2.11/0.68  fof(f43,plain,(
% 2.11/0.68    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 2.11/0.68    inference(cnf_transformation,[],[f1])).
% 2.11/0.68  fof(f590,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_36),
% 2.11/0.68    inference(avatar_component_clause,[],[f589])).
% 2.11/0.68  fof(f624,plain,(
% 2.11/0.68    ~spl4_19 | ~spl4_29 | spl4_36 | ~spl4_5 | ~spl4_10 | ~spl4_23),
% 2.11/0.68    inference(avatar_split_clause,[],[f623,f321,f170,f135,f589,f403,f298])).
% 2.11/0.68  fof(f623,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_1(sK2)) ) | (~spl4_5 | ~spl4_10 | ~spl4_23)),
% 2.11/0.68    inference(superposition,[],[f335,f556])).
% 2.11/0.68  fof(f335,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f332])).
% 2.11/0.68  fof(f332,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.11/0.68    inference(superposition,[],[f57,f55])).
% 2.11/0.68  fof(f57,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f26])).
% 2.11/0.68  fof(f26,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.11/0.68    inference(flattening,[],[f25])).
% 2.11/0.68  fof(f25,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.11/0.68    inference(ennf_transformation,[],[f8])).
% 2.11/0.68  fof(f8,axiom,(
% 2.11/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.11/0.68  fof(f562,plain,(
% 2.11/0.68    ~spl4_5 | spl4_16),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f561])).
% 2.11/0.68  fof(f561,plain,(
% 2.11/0.68    $false | (~spl4_5 | spl4_16)),
% 2.11/0.68    inference(subsumption_resolution,[],[f509,f243])).
% 2.11/0.68  fof(f243,plain,(
% 2.11/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl4_16),
% 2.11/0.68    inference(avatar_component_clause,[],[f241])).
% 2.11/0.68  fof(f509,plain,(
% 2.11/0.68    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 2.11/0.68    inference(forward_demodulation,[],[f495,f63])).
% 2.11/0.68  fof(f495,plain,(
% 2.11/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_5),
% 2.11/0.68    inference(superposition,[],[f33,f137])).
% 2.11/0.68  fof(f33,plain,(
% 2.11/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f527,plain,(
% 2.11/0.68    ~spl4_9 | spl4_10 | spl4_8 | ~spl4_5),
% 2.11/0.68    inference(avatar_split_clause,[],[f520,f135,f148,f170,f166])).
% 2.11/0.68  fof(f166,plain,(
% 2.11/0.68    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 2.11/0.68  fof(f148,plain,(
% 2.11/0.68    spl4_8 <=> k1_xboole_0 = sK1),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 2.11/0.68  fof(f520,plain,(
% 2.11/0.68    k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 2.11/0.68    inference(resolution,[],[f491,f113])).
% 2.11/0.68  fof(f113,plain,(
% 2.11/0.68    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 2.11/0.68    inference(forward_demodulation,[],[f66,f62])).
% 2.11/0.68  fof(f66,plain,(
% 2.11/0.68    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 2.11/0.68    inference(equality_resolution,[],[f46])).
% 2.11/0.68  fof(f46,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f18])).
% 2.11/0.68  fof(f491,plain,(
% 2.11/0.68    v1_funct_2(sK3,sK1,k1_xboole_0) | ~spl4_5),
% 2.11/0.68    inference(superposition,[],[f28,f137])).
% 2.11/0.68  fof(f28,plain,(
% 2.11/0.68    v1_funct_2(sK3,sK1,sK0)),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f526,plain,(
% 2.11/0.68    ~spl4_5 | spl4_9),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f523])).
% 2.11/0.68  fof(f523,plain,(
% 2.11/0.68    $false | (~spl4_5 | spl4_9)),
% 2.11/0.68    inference(subsumption_resolution,[],[f168,f507])).
% 2.11/0.68  fof(f507,plain,(
% 2.11/0.68    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 2.11/0.68    inference(forward_demodulation,[],[f492,f62])).
% 2.11/0.68  fof(f492,plain,(
% 2.11/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | ~spl4_5),
% 2.11/0.68    inference(superposition,[],[f29,f137])).
% 2.11/0.68  fof(f29,plain,(
% 2.11/0.68    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f168,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl4_9),
% 2.11/0.68    inference(avatar_component_clause,[],[f166])).
% 2.11/0.68  fof(f490,plain,(
% 2.11/0.68    ~spl4_32),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f489])).
% 2.11/0.68  fof(f489,plain,(
% 2.11/0.68    $false | ~spl4_32),
% 2.11/0.68    inference(subsumption_resolution,[],[f35,f438])).
% 2.11/0.68  fof(f438,plain,(
% 2.11/0.68    v2_funct_1(sK2) | ~spl4_32),
% 2.11/0.68    inference(avatar_component_clause,[],[f436])).
% 2.11/0.68  fof(f35,plain,(
% 2.11/0.68    ~v2_funct_1(sK2)),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f481,plain,(
% 2.11/0.68    ~spl4_5 | ~spl4_24 | spl4_29),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f480])).
% 2.11/0.68  fof(f480,plain,(
% 2.11/0.68    $false | (~spl4_5 | ~spl4_24 | spl4_29)),
% 2.11/0.68    inference(subsumption_resolution,[],[f405,f479])).
% 2.11/0.68  fof(f479,plain,(
% 2.11/0.68    v1_funct_1(k1_xboole_0) | (~spl4_5 | ~spl4_24)),
% 2.11/0.68    inference(forward_demodulation,[],[f463,f58])).
% 2.11/0.68  fof(f463,plain,(
% 2.11/0.68    v1_funct_1(k6_partfun1(k1_xboole_0)) | (~spl4_5 | ~spl4_24)),
% 2.11/0.68    inference(superposition,[],[f349,f137])).
% 2.11/0.68  fof(f349,plain,(
% 2.11/0.68    v1_funct_1(k6_partfun1(sK0)) | ~spl4_24),
% 2.11/0.68    inference(avatar_component_clause,[],[f347])).
% 2.11/0.68  fof(f347,plain,(
% 2.11/0.68    spl4_24 <=> v1_funct_1(k6_partfun1(sK0))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.11/0.68  fof(f405,plain,(
% 2.11/0.68    ~v1_funct_1(k1_xboole_0) | spl4_29),
% 2.11/0.68    inference(avatar_component_clause,[],[f403])).
% 2.11/0.68  fof(f447,plain,(
% 2.11/0.68    spl4_33),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f444])).
% 2.11/0.68  fof(f444,plain,(
% 2.11/0.68    $false | spl4_33),
% 2.11/0.68    inference(unit_resulting_resolution,[],[f60,f442])).
% 2.11/0.68  fof(f442,plain,(
% 2.11/0.68    ~v2_funct_1(k6_partfun1(sK0)) | spl4_33),
% 2.11/0.68    inference(avatar_component_clause,[],[f440])).
% 2.11/0.68  fof(f440,plain,(
% 2.11/0.68    spl4_33 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 2.11/0.68  fof(f443,plain,(
% 2.11/0.68    spl4_32 | spl4_5 | ~spl4_19 | ~spl4_11 | ~spl4_3 | ~spl4_20 | ~spl4_13 | ~spl4_6 | ~spl4_33 | ~spl4_18),
% 2.11/0.68    inference(avatar_split_clause,[],[f433,f275,f440,f140,f205,f302,f127,f191,f298,f135,f436])).
% 2.11/0.68  fof(f191,plain,(
% 2.11/0.68    spl4_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 2.11/0.68  fof(f127,plain,(
% 2.11/0.68    spl4_3 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.11/0.68  fof(f302,plain,(
% 2.11/0.68    spl4_20 <=> v1_funct_1(sK3)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 2.11/0.68  fof(f205,plain,(
% 2.11/0.68    spl4_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.11/0.68  fof(f140,plain,(
% 2.11/0.68    spl4_6 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 2.11/0.68  fof(f275,plain,(
% 2.11/0.68    spl4_18 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.11/0.68  fof(f433,plain,(
% 2.11/0.68    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl4_18),
% 2.11/0.68    inference(superposition,[],[f51,f277])).
% 2.11/0.68  fof(f277,plain,(
% 2.11/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_18),
% 2.11/0.68    inference(avatar_component_clause,[],[f275])).
% 2.11/0.68  fof(f350,plain,(
% 2.11/0.68    ~spl4_19 | ~spl4_11 | ~spl4_20 | ~spl4_13 | spl4_24 | ~spl4_18),
% 2.11/0.68    inference(avatar_split_clause,[],[f343,f275,f347,f205,f302,f191,f298])).
% 2.11/0.68  fof(f343,plain,(
% 2.11/0.68    v1_funct_1(k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_18),
% 2.11/0.68    inference(superposition,[],[f56,f277])).
% 2.11/0.68  fof(f56,plain,(
% 2.11/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f26])).
% 2.11/0.68  fof(f345,plain,(
% 2.11/0.68    ~spl4_19 | ~spl4_11 | ~spl4_20 | ~spl4_13 | spl4_23 | ~spl4_18),
% 2.11/0.68    inference(avatar_split_clause,[],[f342,f275,f321,f205,f302,f191,f298])).
% 2.11/0.68  fof(f342,plain,(
% 2.11/0.68    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_18),
% 2.11/0.68    inference(superposition,[],[f55,f277])).
% 2.11/0.68  fof(f336,plain,(
% 2.11/0.68    spl4_17),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f325])).
% 2.11/0.68  fof(f325,plain,(
% 2.11/0.68    $false | spl4_17),
% 2.11/0.68    inference(unit_resulting_resolution,[],[f31,f27,f29,f33,f273,f57])).
% 2.11/0.68  fof(f273,plain,(
% 2.11/0.68    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_17),
% 2.11/0.68    inference(avatar_component_clause,[],[f271])).
% 2.11/0.68  fof(f271,plain,(
% 2.11/0.68    spl4_17 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 2.11/0.68  fof(f27,plain,(
% 2.11/0.68    v1_funct_1(sK3)),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f31,plain,(
% 2.11/0.68    v1_funct_1(sK2)),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f318,plain,(
% 2.11/0.68    spl4_20),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f317])).
% 2.11/0.68  fof(f317,plain,(
% 2.11/0.68    $false | spl4_20),
% 2.11/0.68    inference(subsumption_resolution,[],[f27,f304])).
% 2.11/0.68  fof(f304,plain,(
% 2.11/0.68    ~v1_funct_1(sK3) | spl4_20),
% 2.11/0.68    inference(avatar_component_clause,[],[f302])).
% 2.11/0.68  fof(f316,plain,(
% 2.11/0.68    spl4_19),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f315])).
% 2.11/0.68  fof(f315,plain,(
% 2.11/0.68    $false | spl4_19),
% 2.11/0.68    inference(subsumption_resolution,[],[f31,f300])).
% 2.11/0.68  fof(f300,plain,(
% 2.11/0.68    ~v1_funct_1(sK2) | spl4_19),
% 2.11/0.68    inference(avatar_component_clause,[],[f298])).
% 2.11/0.68  fof(f278,plain,(
% 2.11/0.68    ~spl4_17 | spl4_18),
% 2.11/0.68    inference(avatar_split_clause,[],[f268,f275,f271])).
% 2.11/0.68  fof(f268,plain,(
% 2.11/0.68    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.11/0.68    inference(resolution,[],[f181,f30])).
% 2.11/0.68  fof(f30,plain,(
% 2.11/0.68    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f181,plain,(
% 2.11/0.68    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 2.11/0.68    inference(resolution,[],[f54,f59])).
% 2.11/0.68  fof(f59,plain,(
% 2.11/0.68    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.11/0.68    inference(definition_unfolding,[],[f38,f37])).
% 2.11/0.68  fof(f38,plain,(
% 2.11/0.68    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.11/0.68    inference(cnf_transformation,[],[f6])).
% 2.11/0.68  fof(f6,axiom,(
% 2.11/0.68    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.11/0.68  fof(f54,plain,(
% 2.11/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f22])).
% 2.11/0.68  fof(f22,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.11/0.68    inference(flattening,[],[f21])).
% 2.11/0.68  fof(f21,plain,(
% 2.11/0.68    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.11/0.68    inference(ennf_transformation,[],[f5])).
% 2.11/0.68  fof(f5,axiom,(
% 2.11/0.68    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.11/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.11/0.68  fof(f248,plain,(
% 2.11/0.68    ~spl4_6 | spl4_7 | spl4_8),
% 2.11/0.68    inference(avatar_split_clause,[],[f246,f148,f144,f140])).
% 2.11/0.68  fof(f144,plain,(
% 2.11/0.68    spl4_7 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.11/0.68  fof(f246,plain,(
% 2.11/0.68    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 2.11/0.68    inference(resolution,[],[f33,f50])).
% 2.11/0.68  fof(f50,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f18])).
% 2.11/0.68  fof(f244,plain,(
% 2.11/0.68    spl4_15 | ~spl4_16 | ~spl4_5 | ~spl4_14),
% 2.11/0.68    inference(avatar_split_clause,[],[f236,f209,f135,f241,f238])).
% 2.11/0.68  fof(f209,plain,(
% 2.11/0.68    spl4_14 <=> sK0 = k1_relat_1(sK2)),
% 2.11/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 2.11/0.68  fof(f236,plain,(
% 2.11/0.68    ( ! [X3] : (k1_xboole_0 != sK0 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(sK2,k1_xboole_0,X3)) ) | ~spl4_14),
% 2.11/0.68    inference(superposition,[],[f112,f211])).
% 2.11/0.68  fof(f211,plain,(
% 2.11/0.68    sK0 = k1_relat_1(sK2) | ~spl4_14),
% 2.11/0.68    inference(avatar_component_clause,[],[f209])).
% 2.11/0.68  fof(f112,plain,(
% 2.11/0.68    ( ! [X2,X3] : (k1_xboole_0 != k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 2.11/0.68    inference(duplicate_literal_removal,[],[f111])).
% 2.11/0.68  fof(f111,plain,(
% 2.11/0.68    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2)) )),
% 2.11/0.68    inference(forward_demodulation,[],[f109,f63])).
% 2.11/0.68  fof(f109,plain,(
% 2.11/0.68    ( ! [X2,X3] : (k1_xboole_0 != k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 2.11/0.68    inference(superposition,[],[f107,f44])).
% 2.11/0.68  fof(f107,plain,(
% 2.11/0.68    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 2.11/0.68    inference(forward_demodulation,[],[f65,f63])).
% 2.11/0.68  fof(f65,plain,(
% 2.11/0.68    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 2.11/0.68    inference(equality_resolution,[],[f47])).
% 2.11/0.68  fof(f47,plain,(
% 2.11/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 2.11/0.68    inference(cnf_transformation,[],[f18])).
% 2.11/0.68  fof(f232,plain,(
% 2.11/0.68    ~spl4_8),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f224])).
% 2.11/0.68  fof(f224,plain,(
% 2.11/0.68    $false | ~spl4_8),
% 2.11/0.68    inference(subsumption_resolution,[],[f34,f150])).
% 2.11/0.68  fof(f150,plain,(
% 2.11/0.68    k1_xboole_0 = sK1 | ~spl4_8),
% 2.11/0.68    inference(avatar_component_clause,[],[f148])).
% 2.11/0.68  fof(f223,plain,(
% 2.11/0.68    spl4_13),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f222])).
% 2.11/0.68  fof(f222,plain,(
% 2.11/0.68    $false | spl4_13),
% 2.11/0.68    inference(subsumption_resolution,[],[f33,f207])).
% 2.11/0.68  fof(f207,plain,(
% 2.11/0.68    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_13),
% 2.11/0.68    inference(avatar_component_clause,[],[f205])).
% 2.11/0.68  fof(f215,plain,(
% 2.11/0.68    spl4_11),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f214])).
% 2.11/0.68  fof(f214,plain,(
% 2.11/0.68    $false | spl4_11),
% 2.11/0.68    inference(subsumption_resolution,[],[f29,f193])).
% 2.11/0.68  fof(f193,plain,(
% 2.11/0.68    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_11),
% 2.11/0.68    inference(avatar_component_clause,[],[f191])).
% 2.11/0.68  fof(f213,plain,(
% 2.11/0.68    ~spl4_13 | spl4_14 | ~spl4_7),
% 2.11/0.68    inference(avatar_split_clause,[],[f202,f144,f209,f205])).
% 2.11/0.68  fof(f202,plain,(
% 2.11/0.68    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 2.11/0.68    inference(superposition,[],[f44,f146])).
% 2.11/0.68  fof(f146,plain,(
% 2.11/0.68    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_7),
% 2.11/0.68    inference(avatar_component_clause,[],[f144])).
% 2.11/0.68  fof(f185,plain,(
% 2.11/0.68    spl4_6),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f184])).
% 2.11/0.68  fof(f184,plain,(
% 2.11/0.68    $false | spl4_6),
% 2.11/0.68    inference(subsumption_resolution,[],[f32,f142])).
% 2.11/0.68  fof(f142,plain,(
% 2.11/0.68    ~v1_funct_2(sK2,sK0,sK1) | spl4_6),
% 2.11/0.68    inference(avatar_component_clause,[],[f140])).
% 2.11/0.68  fof(f32,plain,(
% 2.11/0.68    v1_funct_2(sK2,sK0,sK1)),
% 2.11/0.68    inference(cnf_transformation,[],[f15])).
% 2.11/0.68  fof(f153,plain,(
% 2.11/0.68    spl4_3),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f152])).
% 2.11/0.68  fof(f152,plain,(
% 2.11/0.68    $false | spl4_3),
% 2.11/0.68    inference(subsumption_resolution,[],[f28,f129])).
% 2.11/0.68  fof(f129,plain,(
% 2.11/0.68    ~v1_funct_2(sK3,sK1,sK0) | spl4_3),
% 2.11/0.68    inference(avatar_component_clause,[],[f127])).
% 2.11/0.68  fof(f98,plain,(
% 2.11/0.68    spl4_2),
% 2.11/0.68    inference(avatar_contradiction_clause,[],[f97])).
% 2.11/0.68  fof(f97,plain,(
% 2.11/0.68    $false | spl4_2),
% 2.11/0.68    inference(subsumption_resolution,[],[f77,f95])).
% 2.11/0.68  fof(f95,plain,(
% 2.11/0.68    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_2),
% 2.11/0.68    inference(avatar_component_clause,[],[f93])).
% 2.11/0.68  fof(f77,plain,(
% 2.11/0.68    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 2.11/0.68    inference(forward_demodulation,[],[f74,f62])).
% 2.11/0.68  fof(f74,plain,(
% 2.11/0.68    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 2.11/0.68    inference(superposition,[],[f59,f58])).
% 2.11/0.68  % SZS output end Proof for theBenchmark
% 2.11/0.68  % (11045)------------------------------
% 2.11/0.68  % (11045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (11045)Termination reason: Refutation
% 2.11/0.68  
% 2.11/0.68  % (11045)Memory used [KB]: 7547
% 2.11/0.68  % (11045)Time elapsed: 0.243 s
% 2.11/0.68  % (11045)------------------------------
% 2.11/0.68  % (11045)------------------------------
% 2.11/0.68  % (11031)Success in time 0.318 s
%------------------------------------------------------------------------------
