%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:51 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 202 expanded)
%              Number of leaves         :   38 (  94 expanded)
%              Depth                    :    6
%              Number of atoms          :  378 ( 590 expanded)
%              Number of equality atoms :   66 ( 108 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f82,f86,f90,f94,f102,f106,f119,f127,f131,f136,f146,f150,f160,f183,f214,f241,f266,f287,f316,f327,f374,f383])).

fof(f383,plain,
    ( ~ spl6_3
    | ~ spl6_9
    | ~ spl6_11
    | spl6_50 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_9
    | ~ spl6_11
    | spl6_50 ),
    inference(unit_resulting_resolution,[],[f81,f57,f373,f89])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f373,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_50 ),
    inference(avatar_component_clause,[],[f372])).

fof(f372,plain,
    ( spl6_50
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f57,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f81,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_9
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f374,plain,
    ( ~ spl6_50
    | ~ spl6_14
    | spl6_23
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f365,f311,f144,f100,f372])).

fof(f100,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f144,plain,
    ( spl6_23
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f311,plain,
    ( spl6_45
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f365,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_14
    | spl6_23
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f364,f145])).

fof(f145,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f144])).

fof(f364,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(trivial_inequality_removal,[],[f355])).

fof(f355,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(superposition,[],[f101,f312])).

fof(f312,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f311])).

fof(f101,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = k2_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f100])).

fof(f327,plain,
    ( ~ spl6_6
    | ~ spl6_10
    | ~ spl6_46 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f324,f69])).

fof(f69,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_6
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f324,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k1_relat_1(sK2)))
    | ~ spl6_10
    | ~ spl6_46 ),
    inference(resolution,[],[f315,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f315,plain,
    ( r2_hidden(sK3(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl6_46
  <=> r2_hidden(sK3(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f316,plain,
    ( spl6_45
    | spl6_46
    | ~ spl6_7
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f303,f285,f72,f314,f311])).

fof(f72,plain,
    ( spl6_7
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f285,plain,
    ( spl6_43
  <=> ! [X0] :
        ( r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0))
        | k1_relat_1(X0) = k1_relat_1(sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f303,plain,
    ( r2_hidden(sK3(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_7
    | ~ spl6_43 ),
    inference(superposition,[],[f286,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f286,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0))
        | k1_relat_1(X0) = k1_relat_1(sK2) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f285])).

fof(f287,plain,
    ( spl6_43
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f275,f264,f125,f56,f285])).

fof(f125,plain,
    ( spl6_19
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f264,plain,
    ( spl6_40
  <=> ! [X0] :
        ( k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2)
        | r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f275,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0))
        | k1_relat_1(X0) = k1_relat_1(sK2) )
    | ~ spl6_3
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f273,f57])).

fof(f273,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0))
        | k1_relat_1(X0) = k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) )
    | ~ spl6_19
    | ~ spl6_40 ),
    inference(superposition,[],[f265,f126])).

fof(f126,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f125])).

fof(f265,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relat_1(X0))
        | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl6_40
    | ~ spl6_12
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f246,f239,f92,f264])).

fof(f92,plain,
    ( spl6_12
  <=> ! [X3,X0,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f239,plain,
    ( spl6_37
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0)
        | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f246,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2)
        | r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relat_1(X0)) )
    | ~ spl6_12
    | ~ spl6_37 ),
    inference(resolution,[],[f240,f93])).

fof(f93,plain,
    ( ! [X2,X0,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),X0)
        | r2_hidden(X2,k1_relat_1(X0)) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f92])).

fof(f240,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0)
        | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,
    ( spl6_37
    | ~ spl6_5
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f217,f212,f148,f64,f239])).

fof(f64,plain,
    ( spl6_5
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f148,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
        | r2_hidden(sK3(X0,X1),X1)
        | k1_relat_1(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f212,plain,
    ( spl6_33
  <=> ! [X1] :
        ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(X1)
        | r2_hidden(k4_tarski(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK5(X1,k1_relset_1(sK1,sK0,sK2))),X1)
        | m1_subset_1(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f217,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0)
        | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) )
    | ~ spl6_5
    | ~ spl6_24
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f215,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X1)
        | r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
        | k1_relat_1(X0) = X1 )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f148])).

fof(f215,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0)
        | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2)
        | ~ r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relset_1(sK1,sK0,sK2)) )
    | ~ spl6_5
    | ~ spl6_33 ),
    inference(resolution,[],[f213,f65])).

fof(f65,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f213,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK1)
        | r2_hidden(k4_tarski(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK5(X1,k1_relset_1(sK1,sK0,sK2))),X1)
        | k1_relset_1(sK1,sK0,sK2) = k1_relat_1(X1) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( spl6_33
    | ~ spl6_25
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f192,f181,f158,f212])).

fof(f158,plain,
    ( spl6_25
  <=> m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f181,plain,
    ( spl6_30
  <=> ! [X3,X5,X4] :
        ( r2_hidden(k4_tarski(sK3(X3,X4),sK5(X3,X4)),X3)
        | k1_relat_1(X3) = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
        | m1_subset_1(sK3(X3,X4),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f192,plain,
    ( ! [X1] :
        ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(X1)
        | r2_hidden(k4_tarski(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK5(X1,k1_relset_1(sK1,sK0,sK2))),X1)
        | m1_subset_1(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK1) )
    | ~ spl6_25
    | ~ spl6_30 ),
    inference(resolution,[],[f182,f159])).

fof(f159,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f158])).

fof(f182,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
        | k1_relat_1(X3) = X4
        | r2_hidden(k4_tarski(sK3(X3,X4),sK5(X3,X4)),X3)
        | m1_subset_1(sK3(X3,X4),X5) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f181])).

fof(f183,plain,
    ( spl6_30
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f152,f148,f104,f181])).

fof(f104,plain,
    ( spl6_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f152,plain,
    ( ! [X4,X5,X3] :
        ( r2_hidden(k4_tarski(sK3(X3,X4),sK5(X3,X4)),X3)
        | k1_relat_1(X3) = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
        | m1_subset_1(sK3(X3,X4),X5) )
    | ~ spl6_15
    | ~ spl6_24 ),
    inference(resolution,[],[f149,f105])).

fof(f105,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | m1_subset_1(X0,X2) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f104])).

fof(f160,plain,
    ( spl6_25
    | ~ spl6_3
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f137,f129,f56,f158])).

fof(f129,plain,
    ( spl6_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f137,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ spl6_3
    | ~ spl6_20 ),
    inference(resolution,[],[f130,f57])).

fof(f130,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f129])).

fof(f150,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f38,f148])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK3(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f146,plain,
    ( ~ spl6_23
    | spl6_4
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f138,f134,f60,f144])).

fof(f60,plain,
    ( spl6_4
  <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f134,plain,
    ( spl6_21
  <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f138,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | spl6_4
    | ~ spl6_21 ),
    inference(superposition,[],[f61,f135])).

fof(f135,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f134])).

fof(f61,plain,
    ( k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f136,plain,
    ( spl6_21
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f132,f117,f56,f134])).

fof(f117,plain,
    ( spl6_17
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f132,plain,
    ( k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(resolution,[],[f118,f57])).

fof(f118,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f117])).

fof(f131,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f43,f129])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f127,plain,(
    spl6_19 ),
    inference(avatar_split_clause,[],[f42,f125])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f119,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f41,f117])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f106,plain,(
    spl6_15 ),
    inference(avatar_split_clause,[],[f44,f104])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f102,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f33,f100])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f94,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f90,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f40,f84])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f82,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f74,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f29,f72])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f70,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f31,f68])).

fof(f31,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f24,f64])).

fof(f24,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f62,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:13:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (812843008)
% 0.14/0.37  ipcrm: permission denied for id (815529987)
% 0.14/0.37  ipcrm: permission denied for id (815562756)
% 0.14/0.37  ipcrm: permission denied for id (815595525)
% 0.14/0.37  ipcrm: permission denied for id (815628294)
% 0.14/0.38  ipcrm: permission denied for id (815661063)
% 0.21/0.38  ipcrm: permission denied for id (815693832)
% 0.21/0.38  ipcrm: permission denied for id (818610185)
% 0.21/0.38  ipcrm: permission denied for id (813006858)
% 0.21/0.38  ipcrm: permission denied for id (813039627)
% 0.21/0.38  ipcrm: permission denied for id (815759372)
% 0.21/0.38  ipcrm: permission denied for id (818642957)
% 0.21/0.38  ipcrm: permission denied for id (819986446)
% 0.21/0.39  ipcrm: permission denied for id (815857679)
% 0.21/0.39  ipcrm: permission denied for id (813170704)
% 0.21/0.39  ipcrm: permission denied for id (818708497)
% 0.21/0.39  ipcrm: permission denied for id (813236242)
% 0.21/0.39  ipcrm: permission denied for id (815923219)
% 0.21/0.39  ipcrm: permission denied for id (815955988)
% 0.21/0.39  ipcrm: permission denied for id (818741269)
% 0.21/0.39  ipcrm: permission denied for id (816021526)
% 0.21/0.40  ipcrm: permission denied for id (816054295)
% 0.21/0.40  ipcrm: permission denied for id (816087064)
% 0.21/0.40  ipcrm: permission denied for id (818774041)
% 0.21/0.40  ipcrm: permission denied for id (816152602)
% 0.21/0.40  ipcrm: permission denied for id (816185371)
% 0.21/0.40  ipcrm: permission denied for id (820019228)
% 0.21/0.40  ipcrm: permission denied for id (820051997)
% 0.21/0.41  ipcrm: permission denied for id (816283678)
% 0.21/0.41  ipcrm: permission denied for id (820084767)
% 0.21/0.41  ipcrm: permission denied for id (813432864)
% 0.21/0.41  ipcrm: permission denied for id (813465633)
% 0.21/0.41  ipcrm: permission denied for id (816349218)
% 0.21/0.41  ipcrm: permission denied for id (818905123)
% 0.21/0.41  ipcrm: permission denied for id (816414756)
% 0.21/0.41  ipcrm: permission denied for id (816447525)
% 0.21/0.42  ipcrm: permission denied for id (818937894)
% 0.21/0.42  ipcrm: permission denied for id (816513063)
% 0.21/0.42  ipcrm: permission denied for id (818970664)
% 0.21/0.42  ipcrm: permission denied for id (813596713)
% 0.21/0.42  ipcrm: permission denied for id (813629482)
% 0.21/0.42  ipcrm: permission denied for id (816578603)
% 0.21/0.42  ipcrm: permission denied for id (816611372)
% 0.21/0.42  ipcrm: permission denied for id (813727789)
% 0.21/0.43  ipcrm: permission denied for id (819003438)
% 0.21/0.43  ipcrm: permission denied for id (820117551)
% 0.21/0.43  ipcrm: permission denied for id (816709680)
% 0.21/0.43  ipcrm: permission denied for id (816742449)
% 0.21/0.43  ipcrm: permission denied for id (819068978)
% 0.21/0.43  ipcrm: permission denied for id (813793332)
% 0.21/0.43  ipcrm: permission denied for id (820183093)
% 0.21/0.44  ipcrm: permission denied for id (816873526)
% 0.21/0.44  ipcrm: permission denied for id (816939064)
% 0.21/0.44  ipcrm: permission denied for id (816971833)
% 0.21/0.44  ipcrm: permission denied for id (817004602)
% 0.21/0.44  ipcrm: permission denied for id (813891643)
% 0.21/0.44  ipcrm: permission denied for id (817037372)
% 0.21/0.44  ipcrm: permission denied for id (819200061)
% 0.21/0.45  ipcrm: permission denied for id (819265599)
% 0.21/0.45  ipcrm: permission denied for id (817168448)
% 0.21/0.45  ipcrm: permission denied for id (814055489)
% 0.21/0.45  ipcrm: permission denied for id (814088258)
% 0.21/0.45  ipcrm: permission denied for id (817201219)
% 0.21/0.45  ipcrm: permission denied for id (819298372)
% 0.21/0.46  ipcrm: permission denied for id (817266757)
% 0.21/0.46  ipcrm: permission denied for id (817299526)
% 0.21/0.46  ipcrm: permission denied for id (814153799)
% 0.21/0.46  ipcrm: permission denied for id (814186568)
% 0.21/0.46  ipcrm: permission denied for id (817332297)
% 0.21/0.46  ipcrm: permission denied for id (819331146)
% 0.21/0.46  ipcrm: permission denied for id (817397835)
% 0.21/0.46  ipcrm: permission denied for id (814252108)
% 0.21/0.47  ipcrm: permission denied for id (820281421)
% 0.21/0.47  ipcrm: permission denied for id (817463374)
% 0.21/0.47  ipcrm: permission denied for id (817496143)
% 0.21/0.47  ipcrm: permission denied for id (814317648)
% 0.21/0.47  ipcrm: permission denied for id (817528913)
% 0.21/0.47  ipcrm: permission denied for id (814350418)
% 0.21/0.47  ipcrm: permission denied for id (820314195)
% 0.21/0.47  ipcrm: permission denied for id (817594452)
% 0.21/0.48  ipcrm: permission denied for id (814448725)
% 0.21/0.48  ipcrm: permission denied for id (814481494)
% 0.21/0.48  ipcrm: permission denied for id (817627223)
% 0.21/0.48  ipcrm: permission denied for id (819429464)
% 0.21/0.48  ipcrm: permission denied for id (814547033)
% 0.21/0.48  ipcrm: permission denied for id (817692762)
% 0.21/0.48  ipcrm: permission denied for id (814579803)
% 0.21/0.48  ipcrm: permission denied for id (820346972)
% 0.21/0.49  ipcrm: permission denied for id (814645341)
% 0.21/0.49  ipcrm: permission denied for id (814678110)
% 0.21/0.49  ipcrm: permission denied for id (814710879)
% 0.21/0.49  ipcrm: permission denied for id (820379744)
% 0.21/0.49  ipcrm: permission denied for id (814743649)
% 0.21/0.49  ipcrm: permission denied for id (817791074)
% 0.21/0.49  ipcrm: permission denied for id (819527779)
% 0.21/0.50  ipcrm: permission denied for id (814841957)
% 0.21/0.50  ipcrm: permission denied for id (814874726)
% 0.21/0.50  ipcrm: permission denied for id (819593319)
% 0.21/0.50  ipcrm: permission denied for id (817922152)
% 0.21/0.50  ipcrm: permission denied for id (814907497)
% 0.21/0.50  ipcrm: permission denied for id (814940268)
% 0.21/0.51  ipcrm: permission denied for id (818020461)
% 0.21/0.51  ipcrm: permission denied for id (818085998)
% 0.21/0.51  ipcrm: permission denied for id (815038575)
% 0.21/0.51  ipcrm: permission denied for id (818118768)
% 0.21/0.51  ipcrm: permission denied for id (818184306)
% 0.21/0.51  ipcrm: permission denied for id (819724403)
% 0.21/0.51  ipcrm: permission denied for id (818249844)
% 0.21/0.52  ipcrm: permission denied for id (820576373)
% 0.21/0.52  ipcrm: permission denied for id (815235190)
% 0.21/0.52  ipcrm: permission denied for id (815267959)
% 0.21/0.52  ipcrm: permission denied for id (819822713)
% 0.21/0.52  ipcrm: permission denied for id (815333498)
% 0.21/0.52  ipcrm: permission denied for id (818413691)
% 0.21/0.52  ipcrm: permission denied for id (815366268)
% 0.21/0.53  ipcrm: permission denied for id (818446461)
% 0.21/0.53  ipcrm: permission denied for id (819888255)
% 0.39/0.64  % (28197)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.39/0.64  % (28195)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.39/0.64  % (28198)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.39/0.65  % (28188)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.39/0.65  % (28197)Refutation found. Thanks to Tanya!
% 0.39/0.65  % SZS status Theorem for theBenchmark
% 0.39/0.65  % (28202)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.39/0.65  % (28190)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.39/0.65  % SZS output start Proof for theBenchmark
% 0.39/0.65  fof(f384,plain,(
% 0.39/0.65    $false),
% 0.39/0.65    inference(avatar_sat_refutation,[],[f58,f62,f66,f70,f74,f82,f86,f90,f94,f102,f106,f119,f127,f131,f136,f146,f150,f160,f183,f214,f241,f266,f287,f316,f327,f374,f383])).
% 0.39/0.66  fof(f383,plain,(
% 0.39/0.66    ~spl6_3 | ~spl6_9 | ~spl6_11 | spl6_50),
% 0.39/0.66    inference(avatar_contradiction_clause,[],[f381])).
% 0.39/0.66  fof(f381,plain,(
% 0.39/0.66    $false | (~spl6_3 | ~spl6_9 | ~spl6_11 | spl6_50)),
% 0.39/0.66    inference(unit_resulting_resolution,[],[f81,f57,f373,f89])).
% 0.39/0.66  fof(f89,plain,(
% 0.39/0.66    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl6_11),
% 0.39/0.66    inference(avatar_component_clause,[],[f88])).
% 0.39/0.66  fof(f88,plain,(
% 0.39/0.66    spl6_11 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.39/0.66  fof(f373,plain,(
% 0.39/0.66    ~v1_relat_1(sK2) | spl6_50),
% 0.39/0.66    inference(avatar_component_clause,[],[f372])).
% 0.39/0.66  fof(f372,plain,(
% 0.39/0.66    spl6_50 <=> v1_relat_1(sK2)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.39/0.66  fof(f57,plain,(
% 0.39/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_3),
% 0.39/0.66    inference(avatar_component_clause,[],[f56])).
% 0.39/0.66  fof(f56,plain,(
% 0.39/0.66    spl6_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.39/0.66  fof(f81,plain,(
% 0.39/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl6_9),
% 0.39/0.66    inference(avatar_component_clause,[],[f80])).
% 0.39/0.66  fof(f80,plain,(
% 0.39/0.66    spl6_9 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.39/0.66  fof(f374,plain,(
% 0.39/0.66    ~spl6_50 | ~spl6_14 | spl6_23 | ~spl6_45),
% 0.39/0.66    inference(avatar_split_clause,[],[f365,f311,f144,f100,f372])).
% 0.39/0.66  fof(f100,plain,(
% 0.39/0.66    spl6_14 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.39/0.66  fof(f144,plain,(
% 0.39/0.66    spl6_23 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.39/0.66  fof(f311,plain,(
% 0.39/0.66    spl6_45 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.39/0.66  fof(f365,plain,(
% 0.39/0.66    ~v1_relat_1(sK2) | (~spl6_14 | spl6_23 | ~spl6_45)),
% 0.39/0.66    inference(subsumption_resolution,[],[f364,f145])).
% 0.39/0.66  fof(f145,plain,(
% 0.39/0.66    k1_xboole_0 != k2_relat_1(sK2) | spl6_23),
% 0.39/0.66    inference(avatar_component_clause,[],[f144])).
% 0.39/0.66  fof(f364,plain,(
% 0.39/0.66    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl6_14 | ~spl6_45)),
% 0.39/0.66    inference(trivial_inequality_removal,[],[f355])).
% 0.39/0.66  fof(f355,plain,(
% 0.39/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl6_14 | ~spl6_45)),
% 0.39/0.66    inference(superposition,[],[f101,f312])).
% 0.39/0.66  fof(f312,plain,(
% 0.39/0.66    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_45),
% 0.39/0.66    inference(avatar_component_clause,[],[f311])).
% 0.39/0.66  fof(f101,plain,(
% 0.39/0.66    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_14),
% 0.39/0.66    inference(avatar_component_clause,[],[f100])).
% 0.39/0.66  fof(f327,plain,(
% 0.39/0.66    ~spl6_6 | ~spl6_10 | ~spl6_46),
% 0.39/0.66    inference(avatar_contradiction_clause,[],[f326])).
% 0.39/0.66  fof(f326,plain,(
% 0.39/0.66    $false | (~spl6_6 | ~spl6_10 | ~spl6_46)),
% 0.39/0.66    inference(subsumption_resolution,[],[f324,f69])).
% 0.39/0.66  fof(f69,plain,(
% 0.39/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl6_6),
% 0.39/0.66    inference(avatar_component_clause,[],[f68])).
% 0.39/0.66  fof(f68,plain,(
% 0.39/0.66    spl6_6 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.39/0.66  fof(f324,plain,(
% 0.39/0.66    ~r1_tarski(k1_xboole_0,sK3(k1_xboole_0,k1_relat_1(sK2))) | (~spl6_10 | ~spl6_46)),
% 0.39/0.66    inference(resolution,[],[f315,f85])).
% 0.39/0.66  fof(f85,plain,(
% 0.39/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) ) | ~spl6_10),
% 0.39/0.66    inference(avatar_component_clause,[],[f84])).
% 0.39/0.66  fof(f84,plain,(
% 0.39/0.66    spl6_10 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.39/0.66  fof(f315,plain,(
% 0.39/0.66    r2_hidden(sK3(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0) | ~spl6_46),
% 0.39/0.66    inference(avatar_component_clause,[],[f314])).
% 0.39/0.66  fof(f314,plain,(
% 0.39/0.66    spl6_46 <=> r2_hidden(sK3(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.39/0.66  fof(f316,plain,(
% 0.39/0.66    spl6_45 | spl6_46 | ~spl6_7 | ~spl6_43),
% 0.39/0.66    inference(avatar_split_clause,[],[f303,f285,f72,f314,f311])).
% 0.39/0.66  fof(f72,plain,(
% 0.39/0.66    spl6_7 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.39/0.66  fof(f285,plain,(
% 0.39/0.66    spl6_43 <=> ! [X0] : (r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0)) | k1_relat_1(X0) = k1_relat_1(sK2))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.39/0.66  fof(f303,plain,(
% 0.39/0.66    r2_hidden(sK3(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK2) | (~spl6_7 | ~spl6_43)),
% 0.39/0.66    inference(superposition,[],[f286,f73])).
% 0.39/0.66  fof(f73,plain,(
% 0.39/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_7),
% 0.39/0.66    inference(avatar_component_clause,[],[f72])).
% 0.39/0.66  fof(f286,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0)) | k1_relat_1(X0) = k1_relat_1(sK2)) ) | ~spl6_43),
% 0.39/0.66    inference(avatar_component_clause,[],[f285])).
% 0.39/0.66  fof(f287,plain,(
% 0.39/0.66    spl6_43 | ~spl6_3 | ~spl6_19 | ~spl6_40),
% 0.39/0.66    inference(avatar_split_clause,[],[f275,f264,f125,f56,f285])).
% 0.39/0.66  fof(f125,plain,(
% 0.39/0.66    spl6_19 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.39/0.66  fof(f264,plain,(
% 0.39/0.66    spl6_40 <=> ! [X0] : (k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relat_1(X0)))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.39/0.66  fof(f275,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0)) | k1_relat_1(X0) = k1_relat_1(sK2)) ) | (~spl6_3 | ~spl6_19 | ~spl6_40)),
% 0.39/0.66    inference(subsumption_resolution,[],[f273,f57])).
% 0.39/0.66  fof(f273,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(sK3(X0,k1_relat_1(sK2)),k1_relat_1(X0)) | k1_relat_1(X0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))) ) | (~spl6_19 | ~spl6_40)),
% 0.39/0.66    inference(superposition,[],[f265,f126])).
% 0.39/0.66  fof(f126,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_19),
% 0.39/0.66    inference(avatar_component_clause,[],[f125])).
% 0.39/0.66  fof(f265,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relat_1(X0)) | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2)) ) | ~spl6_40),
% 0.39/0.66    inference(avatar_component_clause,[],[f264])).
% 0.39/0.66  fof(f266,plain,(
% 0.39/0.66    spl6_40 | ~spl6_12 | ~spl6_37),
% 0.39/0.66    inference(avatar_split_clause,[],[f246,f239,f92,f264])).
% 0.39/0.66  fof(f92,plain,(
% 0.39/0.66    spl6_12 <=> ! [X3,X0,X2] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0)))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.39/0.66  fof(f239,plain,(
% 0.39/0.66    spl6_37 <=> ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0) | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.39/0.66  fof(f246,plain,(
% 0.39/0.66    ( ! [X0] : (k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) | r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relat_1(X0))) ) | (~spl6_12 | ~spl6_37)),
% 0.39/0.66    inference(resolution,[],[f240,f93])).
% 0.39/0.66  fof(f93,plain,(
% 0.39/0.66    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) ) | ~spl6_12),
% 0.39/0.66    inference(avatar_component_clause,[],[f92])).
% 0.39/0.66  fof(f240,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0) | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2)) ) | ~spl6_37),
% 0.39/0.66    inference(avatar_component_clause,[],[f239])).
% 0.39/0.66  fof(f241,plain,(
% 0.39/0.66    spl6_37 | ~spl6_5 | ~spl6_24 | ~spl6_33),
% 0.39/0.66    inference(avatar_split_clause,[],[f217,f212,f148,f64,f239])).
% 0.39/0.66  fof(f64,plain,(
% 0.39/0.66    spl6_5 <=> ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.39/0.66  fof(f148,plain,(
% 0.39/0.66    spl6_24 <=> ! [X1,X0] : (r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.39/0.66  fof(f212,plain,(
% 0.39/0.66    spl6_33 <=> ! [X1] : (k1_relset_1(sK1,sK0,sK2) = k1_relat_1(X1) | r2_hidden(k4_tarski(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK5(X1,k1_relset_1(sK1,sK0,sK2))),X1) | m1_subset_1(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK1))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.39/0.66  fof(f217,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0) | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2)) ) | (~spl6_5 | ~spl6_24 | ~spl6_33)),
% 0.39/0.66    inference(subsumption_resolution,[],[f215,f149])).
% 0.39/0.66  fof(f149,plain,(
% 0.39/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | k1_relat_1(X0) = X1) ) | ~spl6_24),
% 0.39/0.66    inference(avatar_component_clause,[],[f148])).
% 0.39/0.66  fof(f215,plain,(
% 0.39/0.66    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK5(X0,k1_relset_1(sK1,sK0,sK2))),X0) | k1_relat_1(X0) = k1_relset_1(sK1,sK0,sK2) | ~r2_hidden(sK3(X0,k1_relset_1(sK1,sK0,sK2)),k1_relset_1(sK1,sK0,sK2))) ) | (~spl6_5 | ~spl6_33)),
% 0.39/0.66    inference(resolution,[],[f213,f65])).
% 0.39/0.66  fof(f65,plain,(
% 0.39/0.66    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) ) | ~spl6_5),
% 0.39/0.66    inference(avatar_component_clause,[],[f64])).
% 0.39/0.66  fof(f213,plain,(
% 0.39/0.66    ( ! [X1] : (m1_subset_1(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK1) | r2_hidden(k4_tarski(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK5(X1,k1_relset_1(sK1,sK0,sK2))),X1) | k1_relset_1(sK1,sK0,sK2) = k1_relat_1(X1)) ) | ~spl6_33),
% 0.39/0.66    inference(avatar_component_clause,[],[f212])).
% 0.39/0.66  fof(f214,plain,(
% 0.39/0.66    spl6_33 | ~spl6_25 | ~spl6_30),
% 0.39/0.66    inference(avatar_split_clause,[],[f192,f181,f158,f212])).
% 0.39/0.66  fof(f158,plain,(
% 0.39/0.66    spl6_25 <=> m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.39/0.66  fof(f181,plain,(
% 0.39/0.66    spl6_30 <=> ! [X3,X5,X4] : (r2_hidden(k4_tarski(sK3(X3,X4),sK5(X3,X4)),X3) | k1_relat_1(X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | m1_subset_1(sK3(X3,X4),X5))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.39/0.66  fof(f192,plain,(
% 0.39/0.66    ( ! [X1] : (k1_relset_1(sK1,sK0,sK2) = k1_relat_1(X1) | r2_hidden(k4_tarski(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK5(X1,k1_relset_1(sK1,sK0,sK2))),X1) | m1_subset_1(sK3(X1,k1_relset_1(sK1,sK0,sK2)),sK1)) ) | (~spl6_25 | ~spl6_30)),
% 0.39/0.66    inference(resolution,[],[f182,f159])).
% 0.39/0.66  fof(f159,plain,(
% 0.39/0.66    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | ~spl6_25),
% 0.39/0.66    inference(avatar_component_clause,[],[f158])).
% 0.39/0.66  fof(f182,plain,(
% 0.39/0.66    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | k1_relat_1(X3) = X4 | r2_hidden(k4_tarski(sK3(X3,X4),sK5(X3,X4)),X3) | m1_subset_1(sK3(X3,X4),X5)) ) | ~spl6_30),
% 0.39/0.66    inference(avatar_component_clause,[],[f181])).
% 0.39/0.66  fof(f183,plain,(
% 0.39/0.66    spl6_30 | ~spl6_15 | ~spl6_24),
% 0.39/0.66    inference(avatar_split_clause,[],[f152,f148,f104,f181])).
% 0.39/0.66  fof(f104,plain,(
% 0.39/0.66    spl6_15 <=> ! [X1,X0,X2] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.39/0.66  fof(f152,plain,(
% 0.39/0.66    ( ! [X4,X5,X3] : (r2_hidden(k4_tarski(sK3(X3,X4),sK5(X3,X4)),X3) | k1_relat_1(X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | m1_subset_1(sK3(X3,X4),X5)) ) | (~spl6_15 | ~spl6_24)),
% 0.39/0.66    inference(resolution,[],[f149,f105])).
% 0.39/0.66  fof(f105,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) ) | ~spl6_15),
% 0.39/0.66    inference(avatar_component_clause,[],[f104])).
% 0.39/0.66  fof(f160,plain,(
% 0.39/0.66    spl6_25 | ~spl6_3 | ~spl6_20),
% 0.39/0.66    inference(avatar_split_clause,[],[f137,f129,f56,f158])).
% 0.39/0.66  fof(f129,plain,(
% 0.39/0.66    spl6_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.39/0.66  fof(f137,plain,(
% 0.39/0.66    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | (~spl6_3 | ~spl6_20)),
% 0.39/0.66    inference(resolution,[],[f130,f57])).
% 0.39/0.66  fof(f130,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) ) | ~spl6_20),
% 0.39/0.66    inference(avatar_component_clause,[],[f129])).
% 0.39/0.66  fof(f150,plain,(
% 0.39/0.66    spl6_24),
% 0.39/0.66    inference(avatar_split_clause,[],[f38,f148])).
% 0.39/0.66  fof(f38,plain,(
% 0.39/0.66    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.39/0.66    inference(cnf_transformation,[],[f4])).
% 0.39/0.66  fof(f4,axiom,(
% 0.39/0.66    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.39/0.66  fof(f146,plain,(
% 0.39/0.66    ~spl6_23 | spl6_4 | ~spl6_21),
% 0.39/0.66    inference(avatar_split_clause,[],[f138,f134,f60,f144])).
% 0.39/0.66  fof(f60,plain,(
% 0.39/0.66    spl6_4 <=> k1_xboole_0 = k2_relset_1(sK1,sK0,sK2)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.39/0.66  fof(f134,plain,(
% 0.39/0.66    spl6_21 <=> k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.39/0.66  fof(f138,plain,(
% 0.39/0.66    k1_xboole_0 != k2_relat_1(sK2) | (spl6_4 | ~spl6_21)),
% 0.39/0.66    inference(superposition,[],[f61,f135])).
% 0.39/0.66  fof(f135,plain,(
% 0.39/0.66    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | ~spl6_21),
% 0.39/0.66    inference(avatar_component_clause,[],[f134])).
% 0.39/0.66  fof(f61,plain,(
% 0.39/0.66    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) | spl6_4),
% 0.39/0.66    inference(avatar_component_clause,[],[f60])).
% 0.39/0.66  fof(f136,plain,(
% 0.39/0.66    spl6_21 | ~spl6_3 | ~spl6_17),
% 0.39/0.66    inference(avatar_split_clause,[],[f132,f117,f56,f134])).
% 0.39/0.66  fof(f117,plain,(
% 0.39/0.66    spl6_17 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.39/0.66    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.39/0.66  fof(f132,plain,(
% 0.39/0.66    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) | (~spl6_3 | ~spl6_17)),
% 0.39/0.66    inference(resolution,[],[f118,f57])).
% 0.39/0.66  fof(f118,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl6_17),
% 0.39/0.66    inference(avatar_component_clause,[],[f117])).
% 0.39/0.66  fof(f131,plain,(
% 0.39/0.66    spl6_20),
% 0.39/0.66    inference(avatar_split_clause,[],[f43,f129])).
% 0.39/0.66  fof(f43,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.39/0.66    inference(cnf_transformation,[],[f21])).
% 0.39/0.66  fof(f21,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.39/0.66    inference(ennf_transformation,[],[f9])).
% 0.39/0.66  fof(f9,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.39/0.66  fof(f127,plain,(
% 0.39/0.66    spl6_19),
% 0.39/0.66    inference(avatar_split_clause,[],[f42,f125])).
% 0.39/0.66  fof(f42,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f20])).
% 0.39/0.66  fof(f20,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.39/0.66    inference(ennf_transformation,[],[f10])).
% 0.39/0.66  fof(f10,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.39/0.66  fof(f119,plain,(
% 0.39/0.66    spl6_17),
% 0.39/0.66    inference(avatar_split_clause,[],[f41,f117])).
% 0.39/0.66  fof(f41,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f19])).
% 0.39/0.66  fof(f19,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.39/0.66    inference(ennf_transformation,[],[f11])).
% 0.39/0.66  fof(f11,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.39/0.66  fof(f106,plain,(
% 0.39/0.66    spl6_15),
% 0.39/0.66    inference(avatar_split_clause,[],[f44,f104])).
% 0.39/0.66  fof(f44,plain,(
% 0.39/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f23])).
% 0.39/0.66  fof(f23,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.39/0.66    inference(flattening,[],[f22])).
% 0.39/0.66  fof(f22,plain,(
% 0.39/0.66    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.39/0.66    inference(ennf_transformation,[],[f2])).
% 0.39/0.66  fof(f2,axiom,(
% 0.39/0.66    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.39/0.66  fof(f102,plain,(
% 0.39/0.66    spl6_14),
% 0.39/0.66    inference(avatar_split_clause,[],[f33,f100])).
% 0.39/0.66  fof(f33,plain,(
% 0.39/0.66    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f16])).
% 0.39/0.66  fof(f16,plain,(
% 0.39/0.66    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.39/0.66    inference(ennf_transformation,[],[f7])).
% 0.39/0.66  fof(f7,axiom,(
% 0.39/0.66    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.39/0.66  fof(f94,plain,(
% 0.39/0.66    spl6_12),
% 0.39/0.66    inference(avatar_split_clause,[],[f46,f92])).
% 0.39/0.66  fof(f46,plain,(
% 0.39/0.66    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 0.39/0.66    inference(equality_resolution,[],[f36])).
% 0.39/0.66  fof(f36,plain,(
% 0.39/0.66    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.39/0.66    inference(cnf_transformation,[],[f4])).
% 0.39/0.66  fof(f90,plain,(
% 0.39/0.66    spl6_11),
% 0.39/0.66    inference(avatar_split_clause,[],[f34,f88])).
% 0.39/0.66  fof(f34,plain,(
% 0.39/0.66    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f17])).
% 0.39/0.66  fof(f17,plain,(
% 0.39/0.66    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.39/0.66    inference(ennf_transformation,[],[f3])).
% 0.39/0.66  fof(f3,axiom,(
% 0.39/0.66    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.39/0.66  fof(f86,plain,(
% 0.39/0.66    spl6_10),
% 0.39/0.66    inference(avatar_split_clause,[],[f40,f84])).
% 0.39/0.66  fof(f40,plain,(
% 0.39/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f18])).
% 0.39/0.66  fof(f18,plain,(
% 0.39/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.39/0.66    inference(ennf_transformation,[],[f8])).
% 0.39/0.66  fof(f8,axiom,(
% 0.39/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.39/0.66  fof(f82,plain,(
% 0.39/0.66    spl6_9),
% 0.39/0.66    inference(avatar_split_clause,[],[f35,f80])).
% 0.39/0.66  fof(f35,plain,(
% 0.39/0.66    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.39/0.66    inference(cnf_transformation,[],[f5])).
% 0.39/0.66  fof(f5,axiom,(
% 0.39/0.66    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.39/0.66  fof(f74,plain,(
% 0.39/0.66    spl6_7),
% 0.39/0.66    inference(avatar_split_clause,[],[f29,f72])).
% 0.39/0.66  fof(f29,plain,(
% 0.39/0.66    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.39/0.66    inference(cnf_transformation,[],[f6])).
% 0.39/0.66  fof(f6,axiom,(
% 0.39/0.66    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.39/0.66  fof(f70,plain,(
% 0.39/0.66    spl6_6),
% 0.39/0.66    inference(avatar_split_clause,[],[f31,f68])).
% 0.39/0.66  fof(f31,plain,(
% 0.39/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.39/0.66    inference(cnf_transformation,[],[f1])).
% 0.39/0.66  fof(f1,axiom,(
% 0.39/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.39/0.66  fof(f66,plain,(
% 0.39/0.66    spl6_5),
% 0.39/0.66    inference(avatar_split_clause,[],[f24,f64])).
% 0.39/0.66  fof(f24,plain,(
% 0.39/0.66    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))) )),
% 0.39/0.66    inference(cnf_transformation,[],[f15])).
% 0.39/0.66  fof(f15,plain,(
% 0.39/0.66    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.39/0.66    inference(flattening,[],[f14])).
% 0.39/0.66  fof(f14,plain,(
% 0.39/0.66    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.39/0.66    inference(ennf_transformation,[],[f13])).
% 0.39/0.66  fof(f13,negated_conjecture,(
% 0.39/0.66    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.39/0.66    inference(negated_conjecture,[],[f12])).
% 0.39/0.66  fof(f12,conjecture,(
% 0.39/0.66    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.39/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.39/0.66  fof(f62,plain,(
% 0.39/0.66    ~spl6_4),
% 0.39/0.66    inference(avatar_split_clause,[],[f26,f60])).
% 0.39/0.66  fof(f26,plain,(
% 0.39/0.66    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.39/0.66    inference(cnf_transformation,[],[f15])).
% 0.39/0.66  fof(f58,plain,(
% 0.39/0.66    spl6_3),
% 0.39/0.66    inference(avatar_split_clause,[],[f25,f56])).
% 0.39/0.66  fof(f25,plain,(
% 0.39/0.66    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.39/0.66    inference(cnf_transformation,[],[f15])).
% 0.39/0.66  % SZS output end Proof for theBenchmark
% 0.39/0.66  % (28197)------------------------------
% 0.39/0.66  % (28197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.66  % (28197)Termination reason: Refutation
% 0.39/0.66  
% 0.39/0.66  % (28197)Memory used [KB]: 10874
% 0.39/0.66  % (28197)Time elapsed: 0.071 s
% 0.39/0.66  % (28197)------------------------------
% 0.39/0.66  % (28197)------------------------------
% 0.39/0.66  % (28207)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.39/0.66  % (28045)Success in time 0.299 s
%------------------------------------------------------------------------------
