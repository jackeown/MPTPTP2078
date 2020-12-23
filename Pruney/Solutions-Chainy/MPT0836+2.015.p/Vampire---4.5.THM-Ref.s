%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 178 expanded)
%              Number of leaves         :   29 (  82 expanded)
%              Depth                    :    6
%              Number of atoms          :  328 ( 518 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f68,f73,f77,f81,f85,f89,f101,f105,f110,f115,f119,f123,f135,f139,f155,f161,f194,f254,f285,f317,f337,f349])).

fof(f349,plain,
    ( ~ spl11_4
    | ~ spl11_49 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl11_4
    | ~ spl11_49 ),
    inference(unit_resulting_resolution,[],[f56,f336])).

fof(f336,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl11_49 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl11_49
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).

fof(f56,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl11_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f337,plain,
    ( spl11_49
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f329,f315,f99,f87,f335])).

fof(f87,plain,
    ( spl11_12
  <=> ! [X0,X2] :
        ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f99,plain,
    ( spl11_15
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f315,plain,
    ( spl11_46
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f329,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ spl11_12
    | ~ spl11_15
    | ~ spl11_46 ),
    inference(subsumption_resolution,[],[f325,f122])).

fof(f122,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f325,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ r2_hidden(sK3,k1_relat_1(sK2)) )
    | ~ spl11_12
    | ~ spl11_46 ),
    inference(resolution,[],[f316,f88])).

fof(f88,plain,
    ( ! [X2,X0] :
        ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
        | ~ r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f316,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) )
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f315])).

fof(f317,plain,
    ( spl11_46
    | ~ spl11_10
    | ~ spl11_41 ),
    inference(avatar_split_clause,[],[f293,f283,f79,f315])).

fof(f79,plain,
    ( spl11_10
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X3,X2),X0)
        | r2_hidden(X2,k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f283,plain,
    ( spl11_41
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0) )
    | ~ spl11_10
    | ~ spl11_41 ),
    inference(resolution,[],[f284,f80])).

fof(f80,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k2_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X3,X2),X0) )
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f284,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(sK2,sK3),k2_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) )
    | ~ spl11_41 ),
    inference(avatar_component_clause,[],[f283])).

fof(f285,plain,
    ( spl11_41
    | ~ spl11_22
    | ~ spl11_37 ),
    inference(avatar_split_clause,[],[f255,f252,f133,f283])).

fof(f133,plain,
    ( spl11_22
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK6(sK2,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f252,plain,
    ( spl11_37
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
        | ~ r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)) )
    | ~ spl11_22
    | ~ spl11_37 ),
    inference(resolution,[],[f253,f134])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK6(sK2,sK3),X0) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f133])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_37 ),
    inference(avatar_component_clause,[],[f252])).

fof(f254,plain,
    ( spl11_37
    | ~ spl11_16
    | ~ spl11_29 ),
    inference(avatar_split_clause,[],[f200,f192,f103,f252])).

fof(f103,plain,
    ( spl11_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f192,plain,
    ( spl11_29
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).

fof(f200,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_16
    | ~ spl11_29 ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_16
    | ~ spl11_29 ),
    inference(superposition,[],[f193,f104])).

fof(f104,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f193,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_29 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,
    ( spl11_29
    | ~ spl11_18
    | ~ spl11_23 ),
    inference(avatar_split_clause,[],[f174,f137,f113,f192])).

fof(f113,plain,
    ( spl11_18
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f137,plain,
    ( spl11_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_18
    | ~ spl11_23 ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_18
    | ~ spl11_23 ),
    inference(superposition,[],[f114,f138])).

fof(f138,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f137])).

fof(f114,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f113])).

fof(f161,plain,
    ( ~ spl11_7
    | ~ spl11_19 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f67,f118])).

fof(f118,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3,X0),sK2)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl11_19
  <=> ! [X0] : ~ r2_hidden(k4_tarski(sK3,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f67,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl11_7
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f155,plain,
    ( ~ spl11_4
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl11_4
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f153,f56])).

fof(f153,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_5
    | ~ spl11_15
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f152,f122])).

fof(f152,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_5
    | ~ spl11_17 ),
    inference(superposition,[],[f69,f109])).

fof(f109,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl11_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f69,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | spl11_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl11_5
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f139,plain,(
    spl11_23 ),
    inference(avatar_split_clause,[],[f34,f137])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f135,plain,
    ( spl11_22
    | ~ spl11_11
    | spl11_14 ),
    inference(avatar_split_clause,[],[f111,f96,f83,f133])).

fof(f83,plain,
    ( spl11_11
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f96,plain,
    ( spl11_14
  <=> m1_subset_1(sK6(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ r2_hidden(sK6(sK2,sK3),X0) )
    | ~ spl11_11
    | spl11_14 ),
    inference(resolution,[],[f97,f84])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X0,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f97,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | spl11_14 ),
    inference(avatar_component_clause,[],[f96])).

fof(f123,plain,
    ( spl11_15
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(avatar_split_clause,[],[f121,f108,f59,f55,f99])).

fof(f121,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl11_4
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f120,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl11_5
    | ~ spl11_17 ),
    inference(superposition,[],[f60,f109])).

fof(f60,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f119,plain,
    ( spl11_19
    | ~ spl11_9
    | spl11_15 ),
    inference(avatar_split_clause,[],[f106,f99,f75,f117])).

fof(f75,plain,
    ( spl11_9
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK3,X0),sK2)
    | ~ spl11_9
    | spl11_15 ),
    inference(resolution,[],[f100,f76])).

fof(f76,plain,
    ( ! [X2,X0,X3] :
        ( r2_hidden(X2,k1_relat_1(X0))
        | ~ r2_hidden(k4_tarski(X2,X3),X0) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f100,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | spl11_15 ),
    inference(avatar_component_clause,[],[f99])).

fof(f115,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f37,f113])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f110,plain,(
    spl11_17 ),
    inference(avatar_split_clause,[],[f33,f108])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f105,plain,(
    spl11_16 ),
    inference(avatar_split_clause,[],[f32,f103])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f101,plain,
    ( ~ spl11_14
    | ~ spl11_15
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f94,f87,f71,f99,f96])).

fof(f71,plain,
    ( spl11_8
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f94,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ m1_subset_1(sK6(sK2,sK3),sK1)
    | ~ spl11_8
    | ~ spl11_12 ),
    inference(resolution,[],[f88,f72])).

fof(f72,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f89,plain,(
    spl11_12 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
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

fof(f85,plain,(
    spl11_11 ),
    inference(avatar_split_clause,[],[f36,f83])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f81,plain,(
    spl11_10 ),
    inference(avatar_split_clause,[],[f41,f79])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
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

fof(f77,plain,(
    spl11_9 ),
    inference(avatar_split_clause,[],[f39,f75])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f73,plain,
    ( ~ spl11_5
    | spl11_8 ),
    inference(avatar_split_clause,[],[f17,f71,f59])).

fof(f17,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f68,plain,
    ( spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f19,f66,f59])).

fof(f19,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f21,f55])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (30828)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (30829)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.46  % (30829)Refutation not found, incomplete strategy% (30829)------------------------------
% 0.20/0.46  % (30829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (30834)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.47  % (30826)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (30821)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (30829)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (30829)Memory used [KB]: 6140
% 0.20/0.47  % (30829)Time elapsed: 0.052 s
% 0.20/0.47  % (30829)------------------------------
% 0.20/0.47  % (30829)------------------------------
% 0.20/0.47  % (30828)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (30820)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (30824)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (30820)Refutation not found, incomplete strategy% (30820)------------------------------
% 0.20/0.48  % (30820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30820)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30820)Memory used [KB]: 10618
% 0.20/0.48  % (30820)Time elapsed: 0.058 s
% 0.20/0.48  % (30820)------------------------------
% 0.20/0.48  % (30820)------------------------------
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f350,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f57,f68,f73,f77,f81,f85,f89,f101,f105,f110,f115,f119,f123,f135,f139,f155,f161,f194,f254,f285,f317,f337,f349])).
% 0.20/0.48  fof(f349,plain,(
% 0.20/0.48    ~spl11_4 | ~spl11_49),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f345])).
% 0.20/0.48  fof(f345,plain,(
% 0.20/0.48    $false | (~spl11_4 | ~spl11_49)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f56,f336])).
% 0.20/0.48  fof(f336,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | ~spl11_49),
% 0.20/0.48    inference(avatar_component_clause,[],[f335])).
% 0.20/0.48  fof(f335,plain,(
% 0.20/0.48    spl11_49 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_49])])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl11_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl11_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.20/0.48  fof(f337,plain,(
% 0.20/0.48    spl11_49 | ~spl11_12 | ~spl11_15 | ~spl11_46),
% 0.20/0.48    inference(avatar_split_clause,[],[f329,f315,f99,f87,f335])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl11_12 <=> ! [X0,X2] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl11_15 <=> r2_hidden(sK3,k1_relat_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    spl11_46 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).
% 0.20/0.48  fof(f329,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))) ) | (~spl11_12 | ~spl11_15 | ~spl11_46)),
% 0.20/0.48    inference(subsumption_resolution,[],[f325,f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relat_1(sK2)) | ~spl11_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f99])).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~r2_hidden(sK3,k1_relat_1(sK2))) ) | (~spl11_12 | ~spl11_46)),
% 0.20/0.48    inference(resolution,[],[f316,f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) ) | ~spl11_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f316,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))) ) | ~spl11_46),
% 0.20/0.48    inference(avatar_component_clause,[],[f315])).
% 0.20/0.48  fof(f317,plain,(
% 0.20/0.48    spl11_46 | ~spl11_10 | ~spl11_41),
% 0.20/0.48    inference(avatar_split_clause,[],[f293,f283,f79,f315])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl11_10 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    spl11_41 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_41])])).
% 0.20/0.48  fof(f293,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(k4_tarski(X2,sK6(sK2,sK3)),X0)) ) | (~spl11_10 | ~spl11_41)),
% 0.20/0.48    inference(resolution,[],[f284,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (r2_hidden(X2,k2_relat_1(X0)) | ~r2_hidden(k4_tarski(X3,X2),X0)) ) | ~spl11_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f79])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK6(sK2,sK3),k2_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))) ) | ~spl11_41),
% 0.20/0.48    inference(avatar_component_clause,[],[f283])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    spl11_41 | ~spl11_22 | ~spl11_37),
% 0.20/0.48    inference(avatar_split_clause,[],[f255,f252,f133,f283])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl11_22 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK6(sK2,sK3),X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    spl11_37 <=> ! [X1,X0,X2] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_37])])).
% 0.20/0.48  fof(f255,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~r2_hidden(sK6(sK2,sK3),k2_relat_1(X0))) ) | (~spl11_22 | ~spl11_37)),
% 0.20/0.48    inference(resolution,[],[f253,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK6(sK2,sK3),X0)) ) | ~spl11_22),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_37),
% 0.20/0.48    inference(avatar_component_clause,[],[f252])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    spl11_37 | ~spl11_16 | ~spl11_29),
% 0.20/0.48    inference(avatar_split_clause,[],[f200,f192,f103,f252])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl11_16 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    spl11_29 <=> ! [X1,X0,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_29])])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl11_16 | ~spl11_29)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f199])).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl11_16 | ~spl11_29)),
% 0.20/0.48    inference(superposition,[],[f193,f104])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f103])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f192])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    spl11_29 | ~spl11_18 | ~spl11_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f174,f137,f113,f192])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl11_18 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    spl11_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl11_18 | ~spl11_23)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f173])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl11_18 | ~spl11_23)),
% 0.20/0.48    inference(superposition,[],[f114,f138])).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f137])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f113])).
% 0.20/0.48  fof(f161,plain,(
% 0.20/0.48    ~spl11_7 | ~spl11_19),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    $false | (~spl11_7 | ~spl11_19)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f67,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,X0),sK2)) ) | ~spl11_19),
% 0.20/0.48    inference(avatar_component_clause,[],[f117])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    spl11_19 <=> ! [X0] : ~r2_hidden(k4_tarski(sK3,X0),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK3,sK4),sK2) | ~spl11_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl11_7 <=> r2_hidden(k4_tarski(sK3,sK4),sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.20/0.48  fof(f155,plain,(
% 0.20/0.48    ~spl11_4 | spl11_5 | ~spl11_15 | ~spl11_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f154])).
% 0.20/0.48  fof(f154,plain,(
% 0.20/0.48    $false | (~spl11_4 | spl11_5 | ~spl11_15 | ~spl11_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f153,f56])).
% 0.20/0.48  fof(f153,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl11_5 | ~spl11_15 | ~spl11_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f152,f122])).
% 0.20/0.48  fof(f152,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (spl11_5 | ~spl11_17)),
% 0.20/0.48    inference(superposition,[],[f69,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl11_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f108])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl11_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | spl11_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl11_5 <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl11_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f137])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.48  fof(f135,plain,(
% 0.20/0.48    spl11_22 | ~spl11_11 | spl11_14),
% 0.20/0.48    inference(avatar_split_clause,[],[f111,f96,f83,f133])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl11_11 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl11_14 <=> m1_subset_1(sK6(sK2,sK3),sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r2_hidden(sK6(sK2,sK3),X0)) ) | (~spl11_11 | spl11_14)),
% 0.20/0.48    inference(resolution,[],[f97,f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) ) | ~spl11_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ~m1_subset_1(sK6(sK2,sK3),sK1) | spl11_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl11_15 | ~spl11_4 | ~spl11_5 | ~spl11_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f121,f108,f59,f55,f99])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relat_1(sK2)) | (~spl11_4 | ~spl11_5 | ~spl11_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f120,f56])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl11_5 | ~spl11_17)),
% 0.20/0.48    inference(superposition,[],[f60,f109])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) | ~spl11_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f59])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl11_19 | ~spl11_9 | spl11_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f106,f99,f75,f117])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl11_9 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,X0),sK2)) ) | (~spl11_9 | spl11_15)),
% 0.20/0.48    inference(resolution,[],[f100,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) ) | ~spl11_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relat_1(sK2)) | spl11_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f99])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl11_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f113])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl11_17),
% 0.20/0.48    inference(avatar_split_clause,[],[f33,f108])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    spl11_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f103])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ~spl11_14 | ~spl11_15 | ~spl11_8 | ~spl11_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f94,f87,f71,f99,f96])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    spl11_8 <=> ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~r2_hidden(sK3,k1_relat_1(sK2)) | ~m1_subset_1(sK6(sK2,sK3),sK1) | (~spl11_8 | ~spl11_12)),
% 0.20/0.48    inference(resolution,[],[f88,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(k4_tarski(sK3,X4),sK2) | ~m1_subset_1(X4,sK1)) ) | ~spl11_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f71])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl11_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f87])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl11_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f83])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    spl11_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f79])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl11_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f75])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.48    inference(equality_resolution,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ~spl11_5 | spl11_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f17,f71,f59])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ( ! [X4] : (~m1_subset_1(X4,sK1) | ~r2_hidden(k4_tarski(sK3,X4),sK2) | ~r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_hidden(X3,k1_relset_1(X0,X1,X2)) <~> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1))) & m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,k1_relset_1(X0,X1,X2)) <=> ? [X4] : (r2_hidden(k4_tarski(X3,X4),X2) & m1_subset_1(X4,X1)))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl11_5 | spl11_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f66,f59])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r2_hidden(k4_tarski(sK3,sK4),sK2) | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl11_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f21,f55])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30828)------------------------------
% 0.20/0.48  % (30828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30828)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30828)Memory used [KB]: 10874
% 0.20/0.48  % (30828)Time elapsed: 0.062 s
% 0.20/0.48  % (30828)------------------------------
% 0.20/0.48  % (30828)------------------------------
% 0.20/0.48  % (30818)Success in time 0.129 s
%------------------------------------------------------------------------------
