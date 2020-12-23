%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 194 expanded)
%              Number of leaves         :   29 (  76 expanded)
%              Depth                    :    9
%              Number of atoms          :  323 ( 600 expanded)
%              Number of equality atoms :   59 ( 100 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f72,f85,f89,f94,f103,f115,f119,f144,f151,f171,f176,f177,f183,f187,f191,f204])).

fof(f204,plain,
    ( ~ spl8_15
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl8_15
    | spl8_17 ),
    inference(subsumption_resolution,[],[f202,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f202,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_15
    | spl8_17 ),
    inference(superposition,[],[f150,f143])).

fof(f143,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_15
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f150,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl8_17
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f191,plain,
    ( ~ spl8_9
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_20
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f189,f186])).

fof(f186,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl8_21
  <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f189,plain,
    ( sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_9
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f188,f114])).

fof(f114,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_9
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f188,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_20 ),
    inference(resolution,[],[f182,f25])).

fof(f25,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f182,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_20
  <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f187,plain,
    ( spl8_21
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f106,f101,f185])).

fof(f101,plain,
    ( spl8_7
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f106,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_7 ),
    inference(resolution,[],[f102,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | k1_funct_1(X0,sK7(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f102,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f183,plain,
    ( spl8_20
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f178,f174,f181])).

fof(f174,plain,
    ( spl8_19
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f178,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f175,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f175,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f174])).

fof(f177,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f176,plain,
    ( spl8_19
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f172,f169,f146,f174])).

fof(f146,plain,
    ( spl8_16
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f169,plain,
    ( spl8_18
  <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f172,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f170,f147])).

fof(f147,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f146])).

fof(f170,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,
    ( spl8_18
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f104,f101,f169])).

fof(f104,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl8_7 ),
    inference(resolution,[],[f102,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f151,plain,
    ( ~ spl8_17
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f137,f92,f70,f149])).

fof(f70,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f92,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f137,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(resolution,[],[f135,f97])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_6 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f93,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f135,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl8_3 ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,
    ( ! [X1] : k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f76,plain,
    ( ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f144,plain,
    ( spl8_14
    | spl8_15
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f79,f70,f66,f142,f139])).

fof(f139,plain,
    ( spl8_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f66,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f75,f67])).

fof(f67,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f75,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f119,plain,
    ( spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f73,f70,f117])).

fof(f117,plain,
    ( spl8_10
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f73,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( spl8_9
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f105,f101,f113])).

fof(f105,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_7 ),
    inference(resolution,[],[f102,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f99,f92,f83,f61,f101])).

fof(f61,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f83,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f99,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f98,f84])).

fof(f84,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f83])).

fof(f98,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f95,f62])).

fof(f62,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f95,plain,
    ( ~ v1_funct_1(sK3)
    | sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f93,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,
    ( spl8_6
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f90,f87,f70,f92])).

fof(f87,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f90,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f88,f77])).

fof(f88,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f26,f87])).

fof(f26,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f80,f70,f83])).

fof(f80,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f78,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f78,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f71,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f72,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f28,f66])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:39:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (5140)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (5152)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (5140)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f63,f68,f72,f85,f89,f94,f103,f115,f119,f144,f151,f171,f176,f177,f183,f187,f191,f204])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    ~spl8_15 | spl8_17),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    $false | (~spl8_15 | spl8_17)),
% 0.21/0.48    inference(subsumption_resolution,[],[f202,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | (~spl8_15 | spl8_17)),
% 0.21/0.48    inference(superposition,[],[f150,f143])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl8_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    spl8_15 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | spl8_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    spl8_17 <=> v1_xboole_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.48  fof(f191,plain,(
% 0.21/0.48    ~spl8_9 | ~spl8_20 | ~spl8_21),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    $false | (~spl8_9 | ~spl8_20 | ~spl8_21)),
% 0.21/0.48    inference(subsumption_resolution,[],[f189,f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_21),
% 0.21/0.48    inference(avatar_component_clause,[],[f185])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl8_21 <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | (~spl8_9 | ~spl8_20)),
% 0.21/0.48    inference(subsumption_resolution,[],[f188,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f113])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl8_9 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_20),
% 0.21/0.48    inference(resolution,[],[f182,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    inference(negated_conjecture,[],[f11])).
% 0.21/0.48  fof(f11,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl8_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl8_20 <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl8_21 | ~spl8_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f101,f185])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl8_7 <=> sP6(sK4,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_7),
% 0.21/0.48    inference(resolution,[],[f102,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | k1_funct_1(X0,sK7(X0,X1,X3)) = X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    sP6(sK4,sK2,sK3) | ~spl8_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    spl8_20 | ~spl8_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f178,f174,f181])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    spl8_19 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl8_19),
% 0.21/0.48    inference(resolution,[],[f175,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl8_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f174])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) | sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl8_19 | ~spl8_16 | ~spl8_18),
% 0.21/0.48    inference(avatar_split_clause,[],[f172,f169,f146,f174])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl8_16 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl8_18 <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    r2_hidden(sK7(sK3,sK2,sK4),sK0) | (~spl8_16 | ~spl8_18)),
% 0.21/0.48    inference(forward_demodulation,[],[f170,f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl8_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f146])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~spl8_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl8_18 | ~spl8_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f101,f169])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~spl8_7),
% 0.21/0.48    inference(resolution,[],[f102,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ~spl8_17 | ~spl8_3 | ~spl8_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f137,f92,f70,f149])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl8_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1) | (~spl8_3 | ~spl8_6)),
% 0.21/0.48    inference(resolution,[],[f135,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl8_6),
% 0.21/0.48    inference(resolution,[],[f93,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f92])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl8_3),
% 0.21/0.48    inference(superposition,[],[f76,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ( ! [X1] : (k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)) ) | ~spl8_3),
% 0.21/0.48    inference(resolution,[],[f71,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f70])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl8_3),
% 0.21/0.48    inference(resolution,[],[f71,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl8_14 | spl8_15 | ~spl8_2 | ~spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f79,f70,f66,f142,f139])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    spl8_14 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl8_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_2 | ~spl8_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f75,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1) | ~spl8_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 0.21/0.48    inference(resolution,[],[f71,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    spl8_10 | ~spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f73,f70,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl8_10 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl8_3),
% 0.21/0.48    inference(resolution,[],[f71,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl8_9 | ~spl8_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f105,f101,f113])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_7),
% 0.21/0.48    inference(resolution,[],[f102,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl8_7 | ~spl8_1 | ~spl8_4 | ~spl8_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f99,f92,f83,f61,f101])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl8_1 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl8_4 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    sP6(sK4,sK2,sK3) | (~spl8_1 | ~spl8_4 | ~spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f98,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl8_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl8_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~v1_funct_1(sK3) | sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.21/0.48    inference(resolution,[],[f93,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | sP6(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl8_6 | ~spl8_3 | ~spl8_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f90,f87,f70,f92])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl8_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_3 | ~spl8_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f88,f77])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl8_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f87])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl8_4 | ~spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f80,f70,f83])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.48    inference(resolution,[],[f71,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl8_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    spl8_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f66])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl8_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f61])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5140)------------------------------
% 0.21/0.48  % (5140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5140)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5140)Memory used [KB]: 6268
% 0.21/0.48  % (5140)Time elapsed: 0.071 s
% 0.21/0.48  % (5140)------------------------------
% 0.21/0.48  % (5140)------------------------------
% 0.21/0.48  % (5136)Success in time 0.118 s
%------------------------------------------------------------------------------
