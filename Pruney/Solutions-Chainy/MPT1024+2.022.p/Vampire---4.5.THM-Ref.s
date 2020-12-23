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
% DateTime   : Thu Dec  3 13:06:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 173 expanded)
%              Number of leaves         :   25 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  287 ( 554 expanded)
%              Number of equality atoms :   53 (  93 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f70,f83,f87,f92,f100,f112,f116,f129,f138,f182,f185,f228,f234])).

fof(f234,plain,(
    ~ spl8_24 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl8_24 ),
    inference(subsumption_resolution,[],[f232,f49])).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f232,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ spl8_24 ),
    inference(resolution,[],[f227,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f227,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl8_24
  <=> r2_hidden(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f228,plain,
    ( spl8_24
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f223,f136,f90,f68,f226])).

fof(f68,plain,
    ( spl8_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f90,plain,
    ( spl8_6
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f136,plain,
    ( spl8_14
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f223,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f221,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f221,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(resolution,[],[f125,f91])).

fof(f91,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(X0,sK1) )
    | ~ spl8_3 ),
    inference(forward_demodulation,[],[f124,f76])).

fof(f76,plain,
    ( ! [X1] : k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f69,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1))
        | r2_hidden(X0,sK1) )
    | ~ spl8_3 ),
    inference(resolution,[],[f75,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f75,plain,
    ( ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f185,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK3)
    | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3)
    | r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f182,plain,
    ( spl8_18
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f101,f98,f180])).

fof(f180,plain,
    ( spl8_18
  <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f98,plain,
    ( spl8_7
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f101,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl8_7 ),
    inference(resolution,[],[f99,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f99,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f138,plain,
    ( spl8_13
    | spl8_14
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f79,f68,f64,f136,f133])).

fof(f133,plain,
    ( spl8_13
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f64,plain,
    ( spl8_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f79,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f74,f65])).

fof(f65,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f74,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f129,plain,
    ( ~ spl8_12
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f119,f110,f98,f127])).

fof(f127,plain,
    ( spl8_12
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f110,plain,
    ( spl8_9
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f119,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_7
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f117,f103])).

fof(f103,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_7 ),
    inference(resolution,[],[f99,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | k1_funct_1(X0,sK7(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_9 ),
    inference(resolution,[],[f111,f24])).

fof(f24,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f111,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,
    ( spl8_10
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f72,f68,f114])).

fof(f114,plain,
    ( spl8_10
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f72,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f112,plain,
    ( spl8_9
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f102,f98,f110])).

fof(f102,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_7 ),
    inference(resolution,[],[f99,f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f100,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f96,f90,f81,f59,f98])).

fof(f59,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f81,plain,
    ( spl8_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f96,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f95,f82])).

fof(f82,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f95,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f93,f60])).

fof(f60,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f93,plain,
    ( ~ v1_funct_1(sK3)
    | sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f91,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f92,plain,
    ( spl8_6
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f88,f85,f68,f90])).

fof(f85,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f88,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f86,f76])).

fof(f86,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f87,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f25,f85])).

fof(f25,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f83,plain,
    ( spl8_4
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f71,f68,f81])).

fof(f71,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f70,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (17567)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (17584)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (17577)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (17580)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (17567)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f61,f66,f70,f83,f87,f92,f100,f112,f116,f129,f138,f182,f185,f228,f234])).
% 0.21/0.47  fof(f234,plain,(
% 0.21/0.47    ~spl8_24),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f233])).
% 0.21/0.47  fof(f233,plain,(
% 0.21/0.47    $false | ~spl8_24),
% 0.21/0.47    inference(subsumption_resolution,[],[f232,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f232,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,sK4) | ~spl8_24),
% 0.21/0.47    inference(resolution,[],[f227,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.47  fof(f227,plain,(
% 0.21/0.47    r2_hidden(sK4,k1_xboole_0) | ~spl8_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f226])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    spl8_24 <=> r2_hidden(sK4,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    spl8_24 | ~spl8_3 | ~spl8_6 | ~spl8_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f223,f136,f90,f68,f226])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl8_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl8_6 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    spl8_14 <=> k1_xboole_0 = sK1),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    r2_hidden(sK4,k1_xboole_0) | (~spl8_3 | ~spl8_6 | ~spl8_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f221,f137])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | ~spl8_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f136])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    r2_hidden(sK4,sK1) | (~spl8_3 | ~spl8_6)),
% 0.21/0.47    inference(resolution,[],[f125,f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f90])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(X0,sK1)) ) | ~spl8_3),
% 0.21/0.47    inference(forward_demodulation,[],[f124,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ( ! [X1] : (k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)) ) | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f69,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1)) | r2_hidden(X0,sK1)) ) | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f75,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f69,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    sK0 != k1_relset_1(sK0,sK1,sK3) | k1_relset_1(sK0,sK1,sK3) != k1_relat_1(sK3) | r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    spl8_18 | ~spl8_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f101,f98,f180])).
% 0.21/0.47  fof(f180,plain,(
% 0.21/0.47    spl8_18 <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl8_7 <=> sP6(sK4,sK2,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~spl8_7),
% 0.21/0.47    inference(resolution,[],[f99,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    sP6(sK4,sK2,sK3) | ~spl8_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    spl8_13 | spl8_14 | ~spl8_2 | ~spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f79,f68,f64,f136,f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    spl8_13 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl8_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | (~spl8_2 | ~spl8_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f65])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK0,sK1) | ~spl8_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f69,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~spl8_12 | ~spl8_7 | ~spl8_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f119,f110,f98,f127])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    spl8_12 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl8_9 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | (~spl8_7 | ~spl8_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f117,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_7),
% 0.21/0.47    inference(resolution,[],[f99,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | k1_funct_1(X0,sK7(X0,X1,X3)) = X3) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_9),
% 0.21/0.47    inference(resolution,[],[f111,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.47    inference(negated_conjecture,[],[f10])).
% 0.21/0.47  fof(f10,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    spl8_10 | ~spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f72,f68,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl8_10 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f69,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl8_9 | ~spl8_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f102,f98,f110])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_7),
% 0.21/0.47    inference(resolution,[],[f99,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl8_7 | ~spl8_1 | ~spl8_4 | ~spl8_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f96,f90,f81,f59,f98])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl8_1 <=> v1_funct_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl8_4 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    sP6(sK4,sK2,sK3) | (~spl8_1 | ~spl8_4 | ~spl8_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f95,f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl8_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f81])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f93,f60])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    v1_funct_1(sK3) | ~spl8_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f59])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~v1_funct_1(sK3) | sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.21/0.47    inference(resolution,[],[f91,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | sP6(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl8_6 | ~spl8_3 | ~spl8_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f88,f85,f68,f90])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl8_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_3 | ~spl8_5)),
% 0.21/0.47    inference(forward_demodulation,[],[f86,f76])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    spl8_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f85])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl8_4 | ~spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f71,f68,f81])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.47    inference(resolution,[],[f69,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl8_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f68])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl8_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl8_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f59])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    v1_funct_1(sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (17567)------------------------------
% 0.21/0.47  % (17567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17567)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (17567)Memory used [KB]: 6268
% 0.21/0.47  % (17567)Time elapsed: 0.058 s
% 0.21/0.47  % (17567)------------------------------
% 0.21/0.47  % (17567)------------------------------
% 0.21/0.47  % (17566)Success in time 0.121 s
%------------------------------------------------------------------------------
