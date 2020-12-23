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
% DateTime   : Thu Dec  3 13:00:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 281 expanded)
%              Number of leaves         :   48 ( 123 expanded)
%              Depth                    :    8
%              Number of atoms          :  481 (1070 expanded)
%              Number of equality atoms :  100 ( 275 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f429,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f95,f99,f103,f107,f109,f116,f122,f132,f165,f171,f208,f215,f234,f246,f250,f262,f297,f327,f329,f331,f333,f365,f379,f383,f391,f392,f393,f404,f428])).

fof(f428,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 != sK0
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f404,plain,
    ( ~ spl4_25
    | ~ spl4_44
    | spl4_24 ),
    inference(avatar_split_clause,[],[f281,f232,f402,f236])).

fof(f236,plain,
    ( spl4_25
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f402,plain,
    ( spl4_44
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f232,plain,
    ( spl4_24
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f281,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | spl4_24 ),
    inference(resolution,[],[f233,f77])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f233,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_24 ),
    inference(avatar_component_clause,[],[f232])).

fof(f393,plain,
    ( k1_xboole_0 != sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f392,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f391,plain,
    ( ~ spl4_3
    | ~ spl4_21
    | spl4_40 ),
    inference(avatar_split_clause,[],[f390,f377,f212,f86])).

fof(f86,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f212,plain,
    ( spl4_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f377,plain,
    ( spl4_40
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f390,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_21
    | spl4_40 ),
    inference(trivial_inequality_removal,[],[f389])).

fof(f389,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_21
    | spl4_40 ),
    inference(forward_demodulation,[],[f388,f213])).

fof(f213,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f388,plain,
    ( sK0 != k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_40 ),
    inference(superposition,[],[f378,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f378,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f377])).

fof(f383,plain,
    ( spl4_31
    | ~ spl4_41
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f370,f86,f381,f264])).

fof(f264,plain,
    ( spl4_31
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f381,plain,
    ( spl4_41
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f370,plain,
    ( ~ v1_xboole_0(sK2)
    | k1_xboole_0 = sK3
    | ~ spl4_3 ),
    inference(resolution,[],[f364,f139])).

fof(f139,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_xboole_0(X5)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f364,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f379,plain,
    ( spl4_2
    | spl4_39
    | ~ spl4_40
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f367,f86,f377,f374,f83])).

fof(f83,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f374,plain,
    ( spl4_39
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f367,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f364,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f365,plain,
    ( spl4_3
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f362,f325,f260,f86])).

fof(f260,plain,
    ( spl4_30
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f325,plain,
    ( spl4_36
  <=> ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f362,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_30
    | ~ spl4_36 ),
    inference(resolution,[],[f326,f261])).

fof(f261,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f260])).

fof(f326,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f325])).

fof(f333,plain,
    ( k1_xboole_0 != sK3
    | sK0 != k1_relat_1(sK3)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f331,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f329,plain,
    ( ~ spl4_7
    | ~ spl4_35 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f102,f323])).

fof(f323,plain,
    ( ! [X2,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl4_35
  <=> ! [X1,X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f102,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f327,plain,
    ( spl4_35
    | spl4_36
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f320,f212,f169,f325,f322])).

fof(f169,plain,
    ( spl4_16
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f320,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(sK0,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_16
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f318,f213])).

fof(f318,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl4_16 ),
    inference(resolution,[],[f192,f170])).

fof(f170,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f169])).

fof(f192,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ r1_tarski(k1_relat_1(X0),X2)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f61,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f297,plain,
    ( spl4_22
    | ~ spl4_28
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f290,f244,f248,f218])).

fof(f218,plain,
    ( spl4_22
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f248,plain,
    ( spl4_28
  <=> v1_funct_2(sK3,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f244,plain,
    ( spl4_27
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f290,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl4_27 ),
    inference(resolution,[],[f245,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f245,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f262,plain,
    ( spl4_30
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f258,f212,f163,f260])).

fof(f163,plain,
    ( spl4_15
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f258,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(superposition,[],[f164,f213])).

fof(f164,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f250,plain,
    ( spl4_28
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f227,f105,f93,f248])).

fof(f93,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f105,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f227,plain,
    ( v1_funct_2(sK3,k1_xboole_0,sK1)
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(superposition,[],[f106,f94])).

fof(f94,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f246,plain,
    ( spl4_27
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f226,f101,f93,f244])).

fof(f226,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f102,f94])).

fof(f234,plain,
    ( ~ spl4_24
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f223,f93,f83,f232])).

fof(f223,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f84,f94])).

fof(f84,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f215,plain,
    ( ~ spl4_7
    | spl4_21
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f210,f204,f212,f101])).

fof(f204,plain,
    ( spl4_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f210,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_20 ),
    inference(superposition,[],[f64,f205])).

fof(f205,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f208,plain,
    ( spl4_20
    | spl4_4
    | ~ spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f201,f101,f105,f90,f204])).

fof(f90,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f201,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f102])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f171,plain,
    ( ~ spl4_7
    | spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f166,f97,f169,f101])).

fof(f97,plain,
    ( spl4_6
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f166,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6 ),
    inference(superposition,[],[f98,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f98,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f165,plain,
    ( spl4_15
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f160,f101,f163])).

fof(f160,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f159,f102])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(global_subsumption,[],[f55,f62,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f132,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f124,f120,f130])).

fof(f130,plain,
    ( spl4_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f120,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(resolution,[],[f121,f52])).

fof(f121,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f117,f114,f120])).

fof(f114,plain,
    ( spl4_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f117,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl4_9 ),
    inference(resolution,[],[f115,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f115,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f111,f114])).

fof(f111,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f110,f51])).

fof(f51,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f109,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f80,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f107,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f45,f105])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f47,f97])).

fof(f47,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f95,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f48,f93,f90])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

% (19864)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f88,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f49,f86,f83,f80])).

fof(f49,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (19870)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (19870)Refutation not found, incomplete strategy% (19870)------------------------------
% 0.21/0.47  % (19870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19863)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (19870)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19870)Memory used [KB]: 1663
% 0.21/0.47  % (19870)Time elapsed: 0.052 s
% 0.21/0.47  % (19870)------------------------------
% 0.21/0.47  % (19870)------------------------------
% 0.21/0.48  % (19857)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (19860)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (19863)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f429,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f88,f95,f99,f103,f107,f109,f116,f122,f132,f165,f171,f208,f215,f234,f246,f250,f262,f297,f327,f329,f331,f333,f365,f379,f383,f391,f392,f393,f404,f428])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 != sK0 | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f404,plain,(
% 0.21/0.49    ~spl4_25 | ~spl4_44 | spl4_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f281,f232,f402,f236])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    spl4_25 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.49  fof(f402,plain,(
% 0.21/0.49    spl4_44 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    spl4_24 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | spl4_24),
% 0.21/0.49    inference(resolution,[],[f233,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.21/0.49    inference(equality_resolution,[],[f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl4_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f232])).
% 0.21/0.49  fof(f393,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f392,plain,(
% 0.21/0.49    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_xboole_0(sK2) | ~v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ~spl4_3 | ~spl4_21 | spl4_40),
% 0.21/0.49    inference(avatar_split_clause,[],[f390,f377,f212,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl4_21 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f377,plain,(
% 0.21/0.49    spl4_40 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.49  fof(f390,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_21 | spl4_40)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f389])).
% 0.21/0.49  fof(f389,plain,(
% 0.21/0.49    sK0 != sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_21 | spl4_40)),
% 0.21/0.49    inference(forward_demodulation,[],[f388,f213])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | ~spl4_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f212])).
% 0.21/0.49  fof(f388,plain,(
% 0.21/0.49    sK0 != k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_40),
% 0.21/0.49    inference(superposition,[],[f378,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f378,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | spl4_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f377])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    spl4_31 | ~spl4_41 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f370,f86,f381,f264])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    spl4_31 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    spl4_41 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.49  fof(f370,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | k1_xboole_0 = sK3 | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f364,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_xboole_0(X5) | k1_xboole_0 = X3) )),
% 0.21/0.49    inference(resolution,[],[f57,f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f86])).
% 0.21/0.49  fof(f379,plain,(
% 0.21/0.49    spl4_2 | spl4_39 | ~spl4_40 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f367,f86,f377,f374,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl4_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    spl4_39 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.49  fof(f367,plain,(
% 0.21/0.49    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | ~spl4_3),
% 0.21/0.49    inference(resolution,[],[f364,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    spl4_3 | ~spl4_30 | ~spl4_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f362,f325,f260,f86])).
% 0.21/0.49  fof(f260,plain,(
% 0.21/0.49    spl4_30 <=> r1_tarski(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    spl4_36 <=> ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl4_30 | ~spl4_36)),
% 0.21/0.49    inference(resolution,[],[f326,f261])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    r1_tarski(sK0,sK0) | ~spl4_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f260])).
% 0.21/0.49  fof(f326,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl4_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f325])).
% 0.21/0.49  fof(f333,plain,(
% 0.21/0.49    k1_xboole_0 != sK3 | sK0 != k1_relat_1(sK3) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK0),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f331,plain,(
% 0.21/0.49    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK1,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    ~spl4_7 | ~spl4_35),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f328])).
% 0.21/0.49  fof(f328,plain,(
% 0.21/0.49    $false | (~spl4_7 | ~spl4_35)),
% 0.21/0.49    inference(subsumption_resolution,[],[f102,f323])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_35),
% 0.21/0.49    inference(avatar_component_clause,[],[f322])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    spl4_35 <=> ! [X1,X2] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f327,plain,(
% 0.21/0.49    spl4_35 | spl4_36 | ~spl4_16 | ~spl4_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f320,f212,f169,f325,f322])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl4_16 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(sK0,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | (~spl4_16 | ~spl4_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f318,f213])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl4_16),
% 0.21/0.49    inference(resolution,[],[f192,f170])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),sK2) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f169])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(k2_relat_1(X0),X1) | ~r1_tarski(k1_relat_1(X0),X2) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.49    inference(resolution,[],[f61,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    spl4_22 | ~spl4_28 | ~spl4_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f290,f244,f248,f218])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl4_22 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    spl4_28 <=> v1_funct_2(sK3,k1_xboole_0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl4_27 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.49  fof(f290,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,k1_xboole_0,sK1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl4_27),
% 0.21/0.49    inference(resolution,[],[f245,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f244])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    spl4_30 | ~spl4_15 | ~spl4_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f258,f212,f163,f260])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl4_15 <=> r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f258,plain,(
% 0.21/0.49    r1_tarski(sK0,sK0) | (~spl4_15 | ~spl4_21)),
% 0.21/0.49    inference(superposition,[],[f164,f213])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK3),sK0) | ~spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f163])).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    spl4_28 | ~spl4_5 | ~spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f227,f105,f93,f248])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    spl4_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    v1_funct_2(sK3,k1_xboole_0,sK1) | (~spl4_5 | ~spl4_8)),
% 0.21/0.49    inference(superposition,[],[f106,f94])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f93])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1) | ~spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f105])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    spl4_27 | ~spl4_5 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f226,f101,f93,f244])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl4_5 | ~spl4_7)),
% 0.21/0.49    inference(superposition,[],[f102,f94])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~spl4_24 | spl4_2 | ~spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f223,f93,f83,f232])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 0.21/0.49    inference(superposition,[],[f84,f94])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,sK0,sK2) | spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f83])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ~spl4_7 | spl4_21 | ~spl4_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f210,f204,f212,f101])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    spl4_20 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_20),
% 0.21/0.49    inference(superposition,[],[f64,f205])).
% 0.21/0.49  fof(f205,plain,(
% 0.21/0.49    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f204])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    spl4_20 | spl4_4 | ~spl4_8 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f201,f101,f105,f90,f204])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f66,f102])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f43])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~spl4_7 | spl4_16 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f166,f97,f169,f101])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl4_6 <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_6),
% 0.21/0.49    inference(superposition,[],[f98,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    spl4_15 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f160,f101,f163])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    r1_tarski(k1_relat_1(sK3),sK0) | ~spl4_7),
% 0.21/0.49    inference(resolution,[],[f159,f102])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k1_relat_1(X0),X1)) )),
% 0.21/0.49    inference(global_subsumption,[],[f55,f62,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl4_12 | ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f124,f120,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    spl4_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_10 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_10),
% 0.21/0.49    inference(resolution,[],[f121,f52])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f117,f114,f120])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f115,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f114])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(resolution,[],[f110,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(resolution,[],[f54,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_1 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f17])).
% 0.21/0.49  fof(f17,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f105])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f101])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f97])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~spl4_4 | spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f93,f90])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  % (19864)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f86,f83,f80])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (19863)------------------------------
% 0.21/0.49  % (19863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (19863)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (19863)Memory used [KB]: 10874
% 0.21/0.49  % (19863)Time elapsed: 0.074 s
% 0.21/0.49  % (19863)------------------------------
% 0.21/0.49  % (19863)------------------------------
% 0.21/0.50  % (19856)Success in time 0.135 s
%------------------------------------------------------------------------------
