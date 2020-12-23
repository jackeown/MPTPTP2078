%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 162 expanded)
%              Number of leaves         :   26 (  74 expanded)
%              Depth                    :    6
%              Number of atoms          :  294 ( 469 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f64,f69,f73,f77,f81,f85,f97,f101,f106,f111,f115,f119,f133,f161,f167,f190,f194,f200,f313,f326])).

fof(f326,plain,
    ( ~ spl11_12
    | ~ spl11_15
    | ~ spl11_45 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_45 ),
    inference(subsumption_resolution,[],[f322,f118])).

fof(f118,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl11_15
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f322,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl11_12
    | ~ spl11_45 ),
    inference(resolution,[],[f312,f84])).

fof(f84,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl11_12
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f312,plain,
    ( ! [X12] : ~ r2_hidden(k4_tarski(X12,sK6(sK2,sK3)),sK2)
    | ~ spl11_45 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl11_45
  <=> ! [X12] : ~ r2_hidden(k4_tarski(X12,sK6(sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).

fof(f313,plain,
    ( spl11_45
    | ~ spl11_4
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f305,f188,f51,f311])).

fof(f51,plain,
    ( spl11_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f188,plain,
    ( spl11_31
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f305,plain,
    ( ! [X12] : ~ r2_hidden(k4_tarski(X12,sK6(sK2,sK3)),sK2)
    | ~ spl11_4
    | ~ spl11_31 ),
    inference(resolution,[],[f189,f52])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f189,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0) )
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f188])).

fof(f200,plain,
    ( ~ spl11_7
    | ~ spl11_19 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f63,f114])).

fof(f114,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3,X0),sK2)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl11_19
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK3,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f63,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl11_7
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f194,plain,
    ( ~ spl11_4
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl11_4
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f192,f52])).

fof(f192,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f191,f118])).

fof(f191,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_5
    | ~ spl11_17 ),
    inference(superposition,[],[f65,f105])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl11_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f65,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl11_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_5
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f190,plain,
    ( spl11_31
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(avatar_split_clause,[],[f172,f165,f75,f188])).

fof(f75,plain,
    ( spl11_10
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X3,X2),X0)
        | r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f165,plain,
    ( spl11_28
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0) )
    | ~ spl11_10
    | ~ spl11_28 ),
    inference(resolution,[],[f166,f76])).

fof(f76,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X3,X2),X0) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(sK2,sK3),k2_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) )
    | ~ spl11_28 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl11_28
    | ~ spl11_22
    | ~ spl11_27 ),
    inference(avatar_split_clause,[],[f162,f159,f131,f165])).

fof(f131,plain,
    ( spl11_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK6(sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f159,plain,
    ( spl11_27
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)) )
    | ~ spl11_22
    | ~ spl11_27 ),
    inference(resolution,[],[f160,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK6(sK2,sK3),X0) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f131])).

fof(f160,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_27 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl11_27
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f121,f109,f99,f159])).

fof(f99,plain,
    ( spl11_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f109,plain,
    ( spl11_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f121,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(superposition,[],[f110,f100])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f110,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f109])).

fof(f133,plain,
    ( spl11_22
    | ~ spl11_11
    | spl11_14 ),
    inference(avatar_split_clause,[],[f107,f92,f79,f131])).

fof(f79,plain,
    ( spl11_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f92,plain,
    ( spl11_14
  <=> m1_subset_1(sK6(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f107,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK6(sK2,sK3),X0) )
    | ~ spl11_11
    | spl11_14 ),
    inference(resolution,[],[f93,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f93,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | spl11_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f119,plain,
    ( spl11_15
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f117,f104,f55,f51,f95])).

fof(f117,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f116,f52])).

fof(f116,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(superposition,[],[f56,f105])).

fof(f56,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f115,plain,
    ( spl11_19
    | ~ spl11_9
    | spl11_15 ),
    inference(avatar_split_clause,[],[f102,f95,f71,f113])).

fof(f71,plain,
    ( spl11_9
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f102,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3,X0),sK2)
    | ~ spl11_9
    | spl11_15 ),
    inference(resolution,[],[f96,f72])).

fof(f72,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X2,X3),X0) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f96,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl11_15 ),
    inference(avatar_component_clause,[],[f95])).

fof(f111,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f32,f109])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f106,plain,(
    spl11_17 ),
    inference(avatar_split_clause,[],[f31,f104])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f30,f99])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f97,plain,
    ( ~ spl11_14
    | ~ spl11_15
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f90,f83,f67,f95,f92])).

fof(f67,plain,
    ( spl11_8
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f90,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(resolution,[],[f84,f68])).

fof(f68,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f85,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f81,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f33,f79])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f77,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f73,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f69,plain,
    ( ~ spl11_5
    | spl11_8 ),
    inference(avatar_split_clause,[],[f15,f67,f55])).

fof(f15,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

fof(f64,plain,
    ( spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f17,f62,f55])).

fof(f17,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f53,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:13:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (32377)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.43  % (32377)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f327,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f53,f64,f69,f73,f77,f81,f85,f97,f101,f106,f111,f115,f119,f133,f161,f167,f190,f194,f200,f313,f326])).
% 0.21/0.43  fof(f326,plain,(
% 0.21/0.43    ~spl11_12 | ~spl11_15 | ~spl11_45),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f325])).
% 0.21/0.43  fof(f325,plain,(
% 0.21/0.43    $false | (~spl11_12 | ~spl11_15 | ~spl11_45)),
% 0.21/0.43    inference(subsumption_resolution,[],[f322,f118])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl11_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f95])).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    spl11_15 <=> r2_hidden(sK3,k1_relat_1(sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.21/0.43  fof(f322,plain,(
% 0.21/0.43    ~r2_hidden(sK3,k1_relat_1(sK2)) | (~spl11_12 | ~spl11_45)),
% 0.21/0.43    inference(resolution,[],[f312,f84])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) ) | ~spl11_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f83])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl11_12 <=> ! [X0,X2] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.43  fof(f312,plain,(
% 0.21/0.43    ( ! [X12] : (~r2_hidden(k4_tarski(X12,sK6(sK2,sK3)),sK2)) ) | ~spl11_45),
% 0.21/0.43    inference(avatar_component_clause,[],[f311])).
% 0.21/0.43  fof(f311,plain,(
% 0.21/0.43    spl11_45 <=> ! [X12] : ~r2_hidden(k4_tarski(X12,sK6(sK2,sK3)),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_45])])).
% 0.21/0.43  fof(f313,plain,(
% 0.21/0.43    spl11_45 | ~spl11_4 | ~spl11_31),
% 0.21/0.43    inference(avatar_split_clause,[],[f305,f188,f51,f311])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl11_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.43  fof(f188,plain,(
% 0.21/0.43    spl11_31 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).
% 0.21/0.43  fof(f305,plain,(
% 0.21/0.43    ( ! [X12] : (~r2_hidden(k4_tarski(X12,sK6(sK2,sK3)),sK2)) ) | (~spl11_4 | ~spl11_31)),
% 0.21/0.43    inference(resolution,[],[f189,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f189,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0)) ) | ~spl11_31),
% 0.21/0.43    inference(avatar_component_clause,[],[f188])).
% 0.21/0.43  fof(f200,plain,(
% 0.21/0.43    ~spl11_7 | ~spl11_19),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f196])).
% 0.21/0.43  fof(f196,plain,(
% 0.21/0.43    $false | (~spl11_7 | ~spl11_19)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f63,f114])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,X0),sK2)) ) | ~spl11_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f113])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    spl11_19 <=> ! [X0] : ~r2_hidden(k4_tarski(sK3,X0),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    r2_hidden(k4_tarski(sK3,sK4),sK2) | ~spl11_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl11_7 <=> r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.43  fof(f194,plain,(
% 0.21/0.43    ~spl11_4 | spl11_5 | ~spl11_15 | ~spl11_17),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f193])).
% 0.21/0.43  fof(f193,plain,(
% 0.21/0.43    $false | (~spl11_4 | spl11_5 | ~spl11_15 | ~spl11_17)),
% 0.21/0.43    inference(subsumption_resolution,[],[f192,f52])).
% 0.21/0.43  fof(f192,plain,(
% 0.21/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl11_5 | ~spl11_15 | ~spl11_17)),
% 0.21/0.43    inference(subsumption_resolution,[],[f191,f118])).
% 0.21/0.43  fof(f191,plain,(
% 0.21/0.43    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl11_5 | ~spl11_17)),
% 0.21/0.43    inference(superposition,[],[f65,f105])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f104])).
% 0.21/0.43  fof(f104,plain,(
% 0.21/0.43    spl11_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | spl11_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl11_5 <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.21/0.43  fof(f190,plain,(
% 0.21/0.43    spl11_31 | ~spl11_10 | ~spl11_28),
% 0.21/0.43    inference(avatar_split_clause,[],[f172,f165,f75,f188])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl11_10 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.21/0.43  fof(f165,plain,(
% 0.21/0.43    spl11_28 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0)) ) | (~spl11_10 | ~spl11_28)),
% 0.21/0.43    inference(resolution,[],[f166,f76])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) ) | ~spl11_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f75])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))) ) | ~spl11_28),
% 0.21/0.43    inference(avatar_component_clause,[],[f165])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    spl11_28 | ~spl11_22 | ~spl11_27),
% 0.21/0.43    inference(avatar_split_clause,[],[f162,f159,f131,f165])).
% 0.21/0.43  fof(f131,plain,(
% 0.21/0.43    spl11_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK6(sK2,sK3),X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 0.21/0.43  fof(f159,plain,(
% 0.21/0.43    spl11_27 <=> ! [X1,X0,X2] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_27])])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(sK6(sK2,sK3),k2_relat_1(X0))) ) | (~spl11_22 | ~spl11_27)),
% 0.21/0.43    inference(resolution,[],[f160,f132])).
% 0.21/0.43  fof(f132,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK6(sK2,sK3),X0)) ) | ~spl11_22),
% 0.21/0.43    inference(avatar_component_clause,[],[f131])).
% 0.21/0.43  fof(f160,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_27),
% 0.21/0.43    inference(avatar_component_clause,[],[f159])).
% 0.21/0.43  fof(f161,plain,(
% 0.21/0.43    spl11_27 | ~spl11_16 | ~spl11_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f121,f109,f99,f159])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl11_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    spl11_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.21/0.43  fof(f121,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl11_16 | ~spl11_18)),
% 0.21/0.43    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl11_16 | ~spl11_18)),
% 0.21/0.43    inference(superposition,[],[f110,f100])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f99])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_18),
% 0.21/0.43    inference(avatar_component_clause,[],[f109])).
% 0.21/0.43  fof(f133,plain,(
% 0.21/0.43    spl11_22 | ~spl11_11 | spl11_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f107,f92,f79,f131])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl11_11 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    spl11_14 <=> m1_subset_1(sK6(sK2,sK3),sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK6(sK2,sK3),X0)) ) | (~spl11_11 | spl11_14)),
% 0.21/0.43    inference(resolution,[],[f93,f80])).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl11_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f79])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ~m1_subset_1(sK6(sK2,sK3),sK1) | spl11_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f92])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    spl11_15 | ~spl11_4 | ~spl11_5 | ~spl11_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f117,f104,f55,f51,f95])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    r2_hidden(sK3,k1_relat_1(sK2)) | (~spl11_4 | ~spl11_5 | ~spl11_17)),
% 0.21/0.43    inference(subsumption_resolution,[],[f116,f52])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl11_5 | ~spl11_17)),
% 0.21/0.43    inference(superposition,[],[f56,f105])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | ~spl11_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    spl11_19 | ~spl11_9 | spl11_15),
% 0.21/0.43    inference(avatar_split_clause,[],[f102,f95,f71,f113])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl11_9 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.21/0.43  fof(f102,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,X0),sK2)) ) | (~spl11_9 | spl11_15)),
% 0.21/0.43    inference(resolution,[],[f96,f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) ) | ~spl11_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f71])).
% 0.21/0.43  fof(f96,plain,(
% 0.21/0.43    ~r2_hidden(sK3,k1_relat_1(sK2)) | spl11_15),
% 0.21/0.43    inference(avatar_component_clause,[],[f95])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    spl11_18),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f109])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    spl11_17),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f104])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    spl11_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f99])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ~spl11_14 | ~spl11_15 | ~spl11_8 | ~spl11_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f90,f83,f67,f95,f92])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl11_8 <=> ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK6(sK2,sK3),sK1) | (~spl11_8 | ~spl11_12)),
% 0.21/0.44    inference(resolution,[],[f84,f68])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl11_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f85,plain,(
% 0.21/0.44    spl11_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f34,f83])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.44    inference(equality_resolution,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    spl11_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f33,f79])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl11_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f75])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.44    inference(equality_resolution,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    spl11_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f35,f71])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.44    inference(equality_resolution,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    ~spl11_5 | spl11_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f67,f55])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,negated_conjecture,(
% 0.21/0.44    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.21/0.44    inference(negated_conjecture,[],[f7])).
% 0.21/0.44  fof(f7,conjecture,(
% 0.21/0.44    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    spl11_5 | spl11_7),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f62,f55])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    r2_hidden(k4_tarski(sK3,sK4),sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl11_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f51])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (32377)------------------------------
% 0.21/0.44  % (32377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (32377)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (32377)Memory used [KB]: 10874
% 0.21/0.44  % (32377)Time elapsed: 0.018 s
% 0.21/0.44  % (32377)------------------------------
% 0.21/0.44  % (32377)------------------------------
% 0.21/0.44  % (32362)Success in time 0.076 s
%------------------------------------------------------------------------------
