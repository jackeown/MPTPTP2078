%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0821+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 159 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   10
%              Number of atoms          :  268 ( 407 expanded)
%              Number of equality atoms :   30 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f51,f56,f61,f82,f99,f114,f115,f131,f150,f154,f189,f213,f218])).

fof(f218,plain,
    ( ~ spl8_11
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl8_11
    | ~ spl8_14 ),
    inference(resolution,[],[f97,f130])).

fof(f130,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl8_14
  <=> r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f97,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_11
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f213,plain,
    ( ~ spl8_4
    | ~ spl8_5
    | spl8_10
    | ~ spl8_14
    | spl8_18 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_5
    | spl8_10
    | ~ spl8_14
    | spl8_18 ),
    inference(subsumption_resolution,[],[f211,f130])).

fof(f211,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ spl8_4
    | ~ spl8_5
    | spl8_10
    | spl8_18 ),
    inference(resolution,[],[f102,f188])).

fof(f188,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl8_18
  <=> r2_hidden(sK5(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f102,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl8_4
    | ~ spl8_5
    | spl8_10 ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(X0,sK1) )
    | spl8_10 ),
    inference(resolution,[],[f94,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f94,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f101,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,sK1)
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f75,f60])).

fof(f60,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl8_5
  <=> k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f75,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relset_1(sK1,sK0,sK2))
        | m1_subset_1(X1,sK1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f55,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl8_4
  <=> m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f189,plain,
    ( ~ spl8_18
    | spl8_8
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f168,f111,f79,f186])).

fof(f79,plain,
    ( spl8_8
  <=> sK1 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f111,plain,
    ( spl8_12
  <=> sP6(sK5(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f168,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | spl8_8
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f165,f81])).

fof(f81,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f165,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK1)
    | sK1 = k1_relat_1(sK2)
    | ~ spl8_12 ),
    inference(resolution,[],[f113,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ sP6(sK5(X0,X1),X0)
      | ~ r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f113,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f154,plain,
    ( ~ spl8_5
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f151,f144])).

fof(f144,plain,
    ( ! [X4] : ~ r2_hidden(k4_tarski(sK3,X4),sK2)
    | ~ spl8_5
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f133,f80])).

fof(f80,plain,
    ( sK1 = k1_relat_1(sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f133,plain,
    ( ! [X4] :
        ( sK1 != k1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) )
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f18,f60])).

fof(f18,plain,(
    ! [X4] :
      ( sK1 != k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <~> k1_relset_1(X1,X0,X2) = X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( ! [X3] :
              ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
                & r2_hidden(X3,X1) )
        <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f151,plain,
    ( r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),sK2)
    | ~ spl8_13 ),
    inference(resolution,[],[f120,f22])).

fof(f22,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f120,plain,
    ( sP6(sK3,sK2)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl8_13
  <=> sP6(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f150,plain,
    ( ~ spl8_2
    | ~ spl8_8
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_8
    | spl8_13 ),
    inference(subsumption_resolution,[],[f148,f119])).

fof(f119,plain,
    ( ~ sP6(sK3,sK2)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f148,plain,
    ( sP6(sK3,sK2)
    | ~ spl8_2
    | ~ spl8_8 ),
    inference(resolution,[],[f135,f46])).

fof(f46,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl8_2
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sP6(X0,sK2) )
    | ~ spl8_8 ),
    inference(superposition,[],[f32,f80])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f131,plain,
    ( spl8_14
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f124,f111,f128])).

fof(f124,plain,
    ( r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
    | ~ spl8_12 ),
    inference(resolution,[],[f113,f33])).

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f115,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | k1_relset_1(sK1,sK0,sK2) != k1_relat_1(sK2)
    | sK1 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f114,plain,
    ( spl8_12
    | spl8_3
    | spl8_8 ),
    inference(avatar_split_clause,[],[f109,f79,f48,f111])).

fof(f48,plain,
    ( spl8_3
  <=> sK1 = k1_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f109,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | spl8_3
    | spl8_8 ),
    inference(subsumption_resolution,[],[f107,f81])).

fof(f107,plain,
    ( sP6(sK5(sK2,sK1),sK2)
    | sK1 = k1_relat_1(sK2)
    | spl8_3 ),
    inference(factoring,[],[f64])).

fof(f64,plain,
    ( ! [X0] :
        ( sP6(sK5(X0,sK1),sK2)
        | sP6(sK5(X0,sK1),X0)
        | k1_relat_1(X0) = sK1 )
    | spl8_3 ),
    inference(resolution,[],[f63,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | sP6(sK5(X0,X1),X0)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | sP6(X0,sK2) )
    | spl8_3 ),
    inference(resolution,[],[f62,f23])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,
    ( ! [X3] :
        ( r2_hidden(k4_tarski(X3,sK4(X3)),sK2)
        | ~ r2_hidden(X3,sK1) )
    | spl8_3 ),
    inference(subsumption_resolution,[],[f19,f50])).

fof(f50,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f19,plain,(
    ! [X3] :
      ( sK1 = k1_relset_1(sK1,sK0,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(k4_tarski(X3,sK4(X3)),sK2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f99,plain,
    ( ~ spl8_10
    | spl8_11
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f90,f58,f53,f96,f92])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ v1_xboole_0(sK1) )
    | ~ spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f74,f60])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relset_1(sK1,sK0,sK2))
        | ~ v1_xboole_0(sK1) )
    | ~ spl8_4 ),
    inference(resolution,[],[f55,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f82,plain,
    ( ~ spl8_8
    | spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f77,f58,f48,f79])).

fof(f77,plain,
    ( sK1 != k1_relat_1(sK2)
    | spl8_3
    | ~ spl8_5 ),
    inference(superposition,[],[f50,f60])).

fof(f61,plain,
    ( spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f40,f35,f58])).

fof(f35,plain,
    ( spl8_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f40,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f56,plain,
    ( spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f39,f35,f53])).

fof(f39,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl8_1 ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f51,plain,
    ( spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f17,f48,f44])).

fof(f17,plain,
    ( sK1 != k1_relset_1(sK1,sK0,sK2)
    | r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
