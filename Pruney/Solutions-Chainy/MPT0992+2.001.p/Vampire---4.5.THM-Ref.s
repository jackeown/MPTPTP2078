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
% DateTime   : Thu Dec  3 13:03:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 405 expanded)
%              Number of leaves         :   60 ( 178 expanded)
%              Depth                    :    9
%              Number of atoms          :  644 (1341 expanded)
%              Number of equality atoms :  111 ( 257 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f844,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f113,f117,f121,f125,f129,f133,f137,f141,f145,f161,f178,f205,f216,f249,f276,f287,f295,f333,f354,f430,f433,f436,f452,f460,f503,f514,f528,f543,f638,f682,f700,f722,f799,f806,f825,f839,f841,f843])).

fof(f843,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != sK2
    | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | ~ v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f841,plain,
    ( k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != sK2
    | sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f839,plain,
    ( spl4_83
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f835,f173,f837])).

fof(f837,plain,
    ( spl4_83
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f173,plain,
    ( spl4_18
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f835,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_18 ),
    inference(resolution,[],[f174,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f174,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f825,plain,
    ( ~ spl4_49
    | spl4_3
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f824,f274,f104,f450])).

fof(f450,plain,
    ( spl4_49
  <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f104,plain,
    ( spl4_3
  <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f274,plain,
    ( spl4_32
  <=> ! [X3] : k2_partfun1(sK0,sK1,sK3,X3) = k7_relat_1(sK3,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f824,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f105,f275])).

fof(f275,plain,
    ( ! [X3] : k2_partfun1(sK0,sK1,sK3,X3) = k7_relat_1(sK3,X3)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f274])).

fof(f105,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f806,plain,
    ( spl4_49
    | ~ spl4_50
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f801,f501,f458,f450])).

fof(f458,plain,
    ( spl4_50
  <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f501,plain,
    ( spl4_51
  <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f801,plain,
    ( m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl4_50
    | ~ spl4_51 ),
    inference(superposition,[],[f502,f798])).

fof(f798,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f458])).

fof(f502,plain,
    ( ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f501])).

fof(f799,plain,
    ( spl4_50
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f796,f698,f115,f458])).

fof(f115,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f698,plain,
    ( spl4_68
  <=> ! [X8] :
        ( ~ r1_tarski(X8,sK0)
        | k1_relat_1(k7_relat_1(sK3,X8)) = X8 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f796,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ spl4_6
    | ~ spl4_68 ),
    inference(resolution,[],[f699,f116])).

fof(f116,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f699,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,sK0)
        | k1_relat_1(k7_relat_1(sK3,X8)) = X8 )
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f698])).

fof(f722,plain,(
    spl4_67 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl4_67 ),
    inference(resolution,[],[f681,f64])).

fof(f64,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f681,plain,
    ( ~ r1_xboole_0(sK2,k1_xboole_0)
    | spl4_67 ),
    inference(avatar_component_clause,[],[f680])).

fof(f680,plain,
    ( spl4_67
  <=> r1_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).

fof(f700,plain,
    ( ~ spl4_22
    | spl4_68
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f695,f636,f698,f195])).

fof(f195,plain,
    ( spl4_22
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f636,plain,
    ( spl4_60
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f695,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,sK0)
        | k1_relat_1(k7_relat_1(sK3,X8)) = X8
        | ~ v1_relat_1(sK3) )
    | ~ spl4_60 ),
    inference(superposition,[],[f74,f637])).

fof(f637,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f636])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f682,plain,
    ( ~ spl4_67
    | ~ spl4_5
    | spl4_19 ),
    inference(avatar_split_clause,[],[f649,f176,f111,f680])).

fof(f111,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f176,plain,
    ( spl4_19
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f649,plain,
    ( ~ r1_xboole_0(sK2,k1_xboole_0)
    | ~ spl4_5
    | spl4_19 ),
    inference(superposition,[],[f177,f112])).

fof(f112,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f177,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f176])).

fof(f638,plain,
    ( ~ spl4_7
    | spl4_4
    | spl4_60
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f629,f123,f636,f108,f119])).

fof(f119,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f108,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f123,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f629,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f383,f124])).

fof(f124,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f383,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_funct_2(X5,X3,X4)
      | k1_relat_1(X5) = X3
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f83,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f543,plain,
    ( spl4_56
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f539,f438,f541])).

fof(f541,plain,
    ( spl4_56
  <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f438,plain,
    ( spl4_47
  <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f539,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl4_47 ),
    inference(resolution,[],[f527,f69])).

fof(f527,plain,
    ( v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f438])).

fof(f528,plain,
    ( spl4_47
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f518,f512,f131,f438])).

fof(f131,plain,
    ( spl4_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f512,plain,
    ( spl4_52
  <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f518,plain,
    ( v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(resolution,[],[f513,f185])).

fof(f185,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_10 ),
    inference(resolution,[],[f72,f132])).

fof(f132,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f513,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f512])).

fof(f514,plain,
    ( ~ spl4_22
    | spl4_52
    | ~ spl4_24
    | ~ spl4_51 ),
    inference(avatar_split_clause,[],[f510,f501,f203,f512,f195])).

fof(f203,plain,
    ( spl4_24
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f510,plain,
    ( m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_relat_1(sK3)
    | ~ spl4_24
    | ~ spl4_51 ),
    inference(superposition,[],[f502,f240])).

fof(f240,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(k7_relat_1(X1,k1_xboole_0))
        | ~ v1_relat_1(X1) )
    | ~ spl4_24 ),
    inference(resolution,[],[f204,f74])).

fof(f204,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f203])).

fof(f503,plain,
    ( ~ spl4_22
    | spl4_51
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f496,f352,f293,f501,f195])).

fof(f293,plain,
    ( spl4_36
  <=> ! [X0] : v1_funct_1(k7_relat_1(sK3,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f352,plain,
    ( spl4_42
  <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f496,plain,
    ( ! [X0] :
        ( m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
        | ~ v1_relat_1(sK3) )
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(resolution,[],[f484,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f484,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X0))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) )
    | ~ spl4_36
    | ~ spl4_42 ),
    inference(resolution,[],[f355,f294])).

fof(f294,plain,
    ( ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f293])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(k7_relat_1(sK3,X0))
        | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))
        | ~ v1_relat_1(k7_relat_1(sK3,X0)) )
    | ~ spl4_42 ),
    inference(resolution,[],[f353,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f353,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f352])).

fof(f460,plain,
    ( ~ spl4_49
    | ~ spl4_50
    | spl4_48 ),
    inference(avatar_split_clause,[],[f455,f447,f458,f450])).

fof(f447,plain,
    ( spl4_48
  <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f455,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK3,sK2))
    | ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_48 ),
    inference(superposition,[],[f448,f81])).

fof(f448,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | spl4_48 ),
    inference(avatar_component_clause,[],[f447])).

fof(f452,plain,
    ( spl4_4
    | ~ spl4_48
    | ~ spl4_49
    | spl4_2
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f444,f274,f101,f450,f447,f108])).

fof(f101,plain,
    ( spl4_2
  <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f444,plain,
    ( ~ m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f443,f275])).

% (26055)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f443,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f441,f275])).

fof(f441,plain,
    ( sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl4_2 ),
    inference(resolution,[],[f85,f102])).

fof(f102,plain,
    ( ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f436,plain,
    ( ~ spl4_36
    | spl4_45 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl4_36
    | spl4_45 ),
    inference(resolution,[],[f426,f294])).

fof(f426,plain,
    ( ~ v1_funct_1(k7_relat_1(sK3,k1_xboole_0))
    | spl4_45 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl4_45
  <=> v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f433,plain,
    ( ~ spl4_22
    | spl4_44 ),
    inference(avatar_split_clause,[],[f431,f422,f195])).

fof(f422,plain,
    ( spl4_44
  <=> v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f431,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_44 ),
    inference(resolution,[],[f423,f73])).

fof(f423,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | spl4_44 ),
    inference(avatar_component_clause,[],[f422])).

fof(f430,plain,
    ( ~ spl4_22
    | ~ spl4_44
    | ~ spl4_45
    | spl4_46
    | ~ spl4_24
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f419,f352,f203,f428,f425,f422,f195])).

fof(f428,plain,
    ( spl4_46
  <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f419,plain,
    ( v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)
    | ~ v1_funct_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ v1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ v1_relat_1(sK3)
    | ~ spl4_24
    | ~ spl4_42 ),
    inference(superposition,[],[f356,f240])).

fof(f356,plain,
    ( ! [X1] :
        ( v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1)
        | ~ v1_funct_1(k7_relat_1(sK3,X1))
        | ~ v1_relat_1(k7_relat_1(sK3,X1)) )
    | ~ spl4_42 ),
    inference(resolution,[],[f353,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f354,plain,
    ( ~ spl4_22
    | spl4_42
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f347,f331,f352,f195])).

fof(f331,plain,
    ( spl4_40
  <=> ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f347,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)
        | ~ v1_relat_1(sK3) )
    | ~ spl4_40 ),
    inference(resolution,[],[f341,f73])).

fof(f341,plain,
    ( ! [X4] :
        ( ~ v1_relat_1(k7_relat_1(sK3,X4))
        | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),sK1) )
    | ~ spl4_40 ),
    inference(resolution,[],[f332,f184])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f82,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f332,plain,
    ( ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f331])).

fof(f333,plain,
    ( ~ spl4_9
    | spl4_40
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f329,f274,f119,f331,f127])).

fof(f127,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f329,plain,
    ( ! [X3] :
        ( m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f322,f275])).

fof(f322,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f91,f120])).

fof(f120,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f295,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_36
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f283,f274,f293,f119,f127])).

fof(f283,plain,
    ( ! [X0] :
        ( v1_funct_1(k7_relat_1(sK3,X0))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3) )
    | ~ spl4_32 ),
    inference(superposition,[],[f90,f275])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f287,plain,
    ( ~ spl4_34
    | spl4_2
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f281,f274,f101,f285])).

fof(f285,plain,
    ( spl4_34
  <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f281,plain,
    ( ~ v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)
    | spl4_2
    | ~ spl4_32 ),
    inference(superposition,[],[f102,f275])).

fof(f276,plain,
    ( ~ spl4_9
    | spl4_32
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f267,f119,f274,f127])).

fof(f267,plain,
    ( ! [X3] :
        ( k2_partfun1(sK0,sK1,sK3,X3) = k7_relat_1(sK3,X3)
        | ~ v1_funct_1(sK3) )
    | ~ spl4_7 ),
    inference(resolution,[],[f89,f120])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f249,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_1 ),
    inference(avatar_split_clause,[],[f247,f98,f119,f127])).

fof(f98,plain,
    ( spl4_1
  <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f247,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(resolution,[],[f90,f99])).

fof(f99,plain,
    ( ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f216,plain,
    ( ~ spl4_7
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl4_7
    | spl4_22 ),
    inference(subsumption_resolution,[],[f120,f214])).

fof(f214,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_22 ),
    inference(resolution,[],[f196,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f196,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f205,plain,
    ( ~ spl4_16
    | spl4_24
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f201,f139,f203,f159])).

fof(f159,plain,
    ( spl4_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f139,plain,
    ( spl4_12
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f201,plain,
    ( ! [X0] :
        ( r1_tarski(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f193,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f193,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f184,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f178,plain,
    ( spl4_18
    | ~ spl4_19
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f171,f115,f176,f173])).

fof(f171,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | v1_xboole_0(sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f71,f116])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f161,plain,
    ( spl4_16
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f153,f135,f159])).

fof(f135,plain,
    ( spl4_11
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f153,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f66,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f66,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f145,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f62,f143])).

fof(f143,plain,
    ( spl4_13
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f62,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f141,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f63,f139])).

fof(f63,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f137,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f61,f135])).

fof(f61,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f133,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f60,f131])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f129,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f54,f127])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
      | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK2,sK0)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f50])).

fof(f50,plain,
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
   => ( ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
        | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK2,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
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

fof(f125,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f55,f123])).

fof(f55,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f121,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f119])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f117,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f57,f115])).

fof(f57,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f113,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f58,f111,f108])).

fof(f58,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f59,f104,f101,f98])).

fof(f59,plain,
    ( ~ m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)
    | ~ v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:10:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (26049)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (26038)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (26056)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (26041)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (26056)Refutation not found, incomplete strategy% (26056)------------------------------
% 0.21/0.47  % (26056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (26056)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (26056)Memory used [KB]: 10618
% 0.21/0.47  % (26056)Time elapsed: 0.052 s
% 0.21/0.47  % (26056)------------------------------
% 0.21/0.47  % (26056)------------------------------
% 0.21/0.48  % (26051)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (26052)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (26039)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (26036)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (26041)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (26035)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (26036)Refutation not found, incomplete strategy% (26036)------------------------------
% 0.21/0.49  % (26036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26036)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26036)Memory used [KB]: 10618
% 0.21/0.49  % (26036)Time elapsed: 0.071 s
% 0.21/0.49  % (26036)------------------------------
% 0.21/0.49  % (26036)------------------------------
% 0.21/0.49  % (26043)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f844,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f106,f113,f117,f121,f125,f129,f133,f137,f141,f145,f161,f178,f205,f216,f249,f276,f287,f295,f333,f354,f430,f433,f436,f452,f460,f503,f514,f528,f543,f638,f682,f700,f722,f799,f806,f825,f839,f841,f843])).
% 0.21/0.50  fof(f843,plain,(
% 0.21/0.50    k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != sK2 | v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | ~v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f841,plain,(
% 0.21/0.50    k1_xboole_0 != k7_relat_1(sK3,k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != sK2 | sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f839,plain,(
% 0.21/0.50    spl4_83 | ~spl4_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f835,f173,f837])).
% 0.21/0.50  fof(f837,plain,(
% 0.21/0.50    spl4_83 <=> k1_xboole_0 = sK2),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    spl4_18 <=> v1_xboole_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.50  fof(f835,plain,(
% 0.21/0.50    k1_xboole_0 = sK2 | ~spl4_18),
% 0.21/0.50    inference(resolution,[],[f174,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    v1_xboole_0(sK2) | ~spl4_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f173])).
% 0.21/0.50  fof(f825,plain,(
% 0.21/0.50    ~spl4_49 | spl4_3 | ~spl4_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f824,f274,f104,f450])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    spl4_49 <=> m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl4_3 <=> m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    spl4_32 <=> ! [X3] : k2_partfun1(sK0,sK1,sK3,X3) = k7_relat_1(sK3,X3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.50  fof(f824,plain,(
% 0.21/0.50    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_3 | ~spl4_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f105,f275])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ( ! [X3] : (k2_partfun1(sK0,sK1,sK3,X3) = k7_relat_1(sK3,X3)) ) | ~spl4_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f274])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f806,plain,(
% 0.21/0.50    spl4_49 | ~spl4_50 | ~spl4_51),
% 0.21/0.50    inference(avatar_split_clause,[],[f801,f501,f458,f450])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    spl4_50 <=> sK2 = k1_relat_1(k7_relat_1(sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.21/0.50  fof(f501,plain,(
% 0.21/0.50    spl4_51 <=> ! [X0] : m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.21/0.50  fof(f801,plain,(
% 0.21/0.50    m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (~spl4_50 | ~spl4_51)),
% 0.21/0.50    inference(superposition,[],[f502,f798])).
% 0.21/0.50  fof(f798,plain,(
% 0.21/0.50    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | ~spl4_50),
% 0.21/0.50    inference(avatar_component_clause,[],[f458])).
% 0.21/0.50  fof(f502,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) ) | ~spl4_51),
% 0.21/0.50    inference(avatar_component_clause,[],[f501])).
% 0.21/0.50  fof(f799,plain,(
% 0.21/0.50    spl4_50 | ~spl4_6 | ~spl4_68),
% 0.21/0.50    inference(avatar_split_clause,[],[f796,f698,f115,f458])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl4_6 <=> r1_tarski(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.50  fof(f698,plain,(
% 0.21/0.50    spl4_68 <=> ! [X8] : (~r1_tarski(X8,sK0) | k1_relat_1(k7_relat_1(sK3,X8)) = X8)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.21/0.50  fof(f796,plain,(
% 0.21/0.50    sK2 = k1_relat_1(k7_relat_1(sK3,sK2)) | (~spl4_6 | ~spl4_68)),
% 0.21/0.50    inference(resolution,[],[f699,f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    r1_tarski(sK2,sK0) | ~spl4_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f699,plain,(
% 0.21/0.50    ( ! [X8] : (~r1_tarski(X8,sK0) | k1_relat_1(k7_relat_1(sK3,X8)) = X8) ) | ~spl4_68),
% 0.21/0.50    inference(avatar_component_clause,[],[f698])).
% 0.21/0.50  fof(f722,plain,(
% 0.21/0.50    spl4_67),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f721])).
% 0.21/0.50  fof(f721,plain,(
% 0.21/0.50    $false | spl4_67),
% 0.21/0.50    inference(resolution,[],[f681,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f681,plain,(
% 0.21/0.50    ~r1_xboole_0(sK2,k1_xboole_0) | spl4_67),
% 0.21/0.50    inference(avatar_component_clause,[],[f680])).
% 0.21/0.50  fof(f680,plain,(
% 0.21/0.50    spl4_67 <=> r1_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_67])])).
% 0.21/0.50  fof(f700,plain,(
% 0.21/0.50    ~spl4_22 | spl4_68 | ~spl4_60),
% 0.21/0.50    inference(avatar_split_clause,[],[f695,f636,f698,f195])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    spl4_22 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.50  fof(f636,plain,(
% 0.21/0.50    spl4_60 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.21/0.50  fof(f695,plain,(
% 0.21/0.50    ( ! [X8] : (~r1_tarski(X8,sK0) | k1_relat_1(k7_relat_1(sK3,X8)) = X8 | ~v1_relat_1(sK3)) ) | ~spl4_60),
% 0.21/0.50    inference(superposition,[],[f74,f637])).
% 0.21/0.50  fof(f637,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | ~spl4_60),
% 0.21/0.50    inference(avatar_component_clause,[],[f636])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 0.21/0.50  fof(f682,plain,(
% 0.21/0.50    ~spl4_67 | ~spl4_5 | spl4_19),
% 0.21/0.50    inference(avatar_split_clause,[],[f649,f176,f111,f680])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl4_5 <=> k1_xboole_0 = sK0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl4_19 <=> r1_xboole_0(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.50  fof(f649,plain,(
% 0.21/0.50    ~r1_xboole_0(sK2,k1_xboole_0) | (~spl4_5 | spl4_19)),
% 0.21/0.50    inference(superposition,[],[f177,f112])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | ~spl4_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f111])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ~r1_xboole_0(sK2,sK0) | spl4_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f176])).
% 0.21/0.50  fof(f638,plain,(
% 0.21/0.50    ~spl4_7 | spl4_4 | spl4_60 | ~spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f629,f123,f636,f108,f119])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl4_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.50  fof(f629,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_8),
% 0.21/0.50    inference(resolution,[],[f383,f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1) | ~spl4_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (~v1_funct_2(X5,X3,X4) | k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f380])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.50    inference(superposition,[],[f83,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.50  fof(f543,plain,(
% 0.21/0.50    spl4_56 | ~spl4_47),
% 0.21/0.50    inference(avatar_split_clause,[],[f539,f438,f541])).
% 0.21/0.50  fof(f541,plain,(
% 0.21/0.50    spl4_56 <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    spl4_47 <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 0.21/0.50  fof(f539,plain,(
% 0.21/0.50    k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) | ~spl4_47),
% 0.21/0.50    inference(resolution,[],[f527,f69])).
% 0.21/0.50  fof(f527,plain,(
% 0.21/0.50    v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) | ~spl4_47),
% 0.21/0.50    inference(avatar_component_clause,[],[f438])).
% 0.21/0.50  fof(f528,plain,(
% 0.21/0.50    spl4_47 | ~spl4_10 | ~spl4_52),
% 0.21/0.50    inference(avatar_split_clause,[],[f518,f512,f131,f438])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl4_10 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.50  fof(f512,plain,(
% 0.21/0.50    spl4_52 <=> m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.21/0.50  fof(f518,plain,(
% 0.21/0.50    v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) | (~spl4_10 | ~spl4_52)),
% 0.21/0.50    inference(resolution,[],[f513,f185])).
% 0.21/0.50  fof(f185,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl4_10),
% 0.21/0.50    inference(resolution,[],[f72,f132])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0) | ~spl4_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.21/0.50  fof(f513,plain,(
% 0.21/0.50    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl4_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f512])).
% 0.21/0.50  fof(f514,plain,(
% 0.21/0.50    ~spl4_22 | spl4_52 | ~spl4_24 | ~spl4_51),
% 0.21/0.50    inference(avatar_split_clause,[],[f510,f501,f203,f512,f195])).
% 0.21/0.50  fof(f203,plain,(
% 0.21/0.50    spl4_24 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.50  fof(f510,plain,(
% 0.21/0.50    m1_subset_1(k7_relat_1(sK3,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~v1_relat_1(sK3) | (~spl4_24 | ~spl4_51)),
% 0.21/0.50    inference(superposition,[],[f502,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ( ! [X1] : (k1_xboole_0 = k1_relat_1(k7_relat_1(X1,k1_xboole_0)) | ~v1_relat_1(X1)) ) | ~spl4_24),
% 0.21/0.50    inference(resolution,[],[f204,f74])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl4_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f203])).
% 0.21/0.50  fof(f503,plain,(
% 0.21/0.50    ~spl4_22 | spl4_51 | ~spl4_36 | ~spl4_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f496,f352,f293,f501,f195])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    spl4_36 <=> ! [X0] : v1_funct_1(k7_relat_1(sK3,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.21/0.50  fof(f352,plain,(
% 0.21/0.50    spl4_42 <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.21/0.50  fof(f496,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) | ~v1_relat_1(sK3)) ) | (~spl4_36 | ~spl4_42)),
% 0.21/0.50    inference(resolution,[],[f484,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.50  fof(f484,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_relat_1(k7_relat_1(sK3,X0)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1)))) ) | (~spl4_36 | ~spl4_42)),
% 0.21/0.50    inference(resolution,[],[f355,f294])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0))) ) | ~spl4_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f293])).
% 0.21/0.50  fof(f355,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_funct_1(k7_relat_1(sK3,X0)) | m1_subset_1(k7_relat_1(sK3,X0),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k7_relat_1(sK3,X0)),sK1))) | ~v1_relat_1(k7_relat_1(sK3,X0))) ) | ~spl4_42),
% 0.21/0.50    inference(resolution,[],[f353,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 0.21/0.50  fof(f353,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1)) ) | ~spl4_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f352])).
% 0.21/0.50  fof(f460,plain,(
% 0.21/0.50    ~spl4_49 | ~spl4_50 | spl4_48),
% 0.21/0.50    inference(avatar_split_clause,[],[f455,f447,f458,f450])).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    spl4_48 <=> sK2 = k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.50  fof(f455,plain,(
% 0.21/0.50    sK2 != k1_relat_1(k7_relat_1(sK3,sK2)) | ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_48),
% 0.21/0.50    inference(superposition,[],[f448,f81])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | spl4_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f447])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    spl4_4 | ~spl4_48 | ~spl4_49 | spl4_2 | ~spl4_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f444,f274,f101,f450,f447,f108])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl4_2 <=> v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    ~m1_subset_1(k7_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | (spl4_2 | ~spl4_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f443,f275])).
% 0.21/0.50  % (26055)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  fof(f443,plain,(
% 0.21/0.50    sK2 != k1_relset_1(sK2,sK1,k7_relat_1(sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | (spl4_2 | ~spl4_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f441,f275])).
% 0.21/0.50  fof(f441,plain,(
% 0.21/0.50    sK2 != k1_relset_1(sK2,sK1,k2_partfun1(sK0,sK1,sK3,sK2)) | k1_xboole_0 = sK1 | ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl4_2),
% 0.21/0.50    inference(resolution,[],[f85,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | spl4_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f53])).
% 0.21/0.50  fof(f436,plain,(
% 0.21/0.50    ~spl4_36 | spl4_45),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    $false | (~spl4_36 | spl4_45)),
% 0.21/0.50    inference(resolution,[],[f426,f294])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    ~v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) | spl4_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f425])).
% 0.21/0.50  fof(f425,plain,(
% 0.21/0.50    spl4_45 <=> v1_funct_1(k7_relat_1(sK3,k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.50  fof(f433,plain,(
% 0.21/0.50    ~spl4_22 | spl4_44),
% 0.21/0.50    inference(avatar_split_clause,[],[f431,f422,f195])).
% 0.21/0.50  fof(f422,plain,(
% 0.21/0.50    spl4_44 <=> v1_relat_1(k7_relat_1(sK3,k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl4_44),
% 0.21/0.50    inference(resolution,[],[f423,f73])).
% 0.21/0.50  fof(f423,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | spl4_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f422])).
% 0.21/0.50  fof(f430,plain,(
% 0.21/0.50    ~spl4_22 | ~spl4_44 | ~spl4_45 | spl4_46 | ~spl4_24 | ~spl4_42),
% 0.21/0.50    inference(avatar_split_clause,[],[f419,f352,f203,f428,f425,f422,f195])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    spl4_46 <=> v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.50  fof(f419,plain,(
% 0.21/0.50    v1_funct_2(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0,sK1) | ~v1_funct_1(k7_relat_1(sK3,k1_xboole_0)) | ~v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) | ~v1_relat_1(sK3) | (~spl4_24 | ~spl4_42)),
% 0.21/0.50    inference(superposition,[],[f356,f240])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    ( ! [X1] : (v1_funct_2(k7_relat_1(sK3,X1),k1_relat_1(k7_relat_1(sK3,X1)),sK1) | ~v1_funct_1(k7_relat_1(sK3,X1)) | ~v1_relat_1(k7_relat_1(sK3,X1))) ) | ~spl4_42),
% 0.21/0.50    inference(resolution,[],[f353,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f354,plain,(
% 0.21/0.50    ~spl4_22 | spl4_42 | ~spl4_40),
% 0.21/0.50    inference(avatar_split_clause,[],[f347,f331,f352,f195])).
% 0.21/0.50  fof(f331,plain,(
% 0.21/0.50    spl4_40 <=> ! [X3] : m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK3,X0)),sK1) | ~v1_relat_1(sK3)) ) | ~spl4_40),
% 0.21/0.50    inference(resolution,[],[f341,f73])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ( ! [X4] : (~v1_relat_1(k7_relat_1(sK3,X4)) | r1_tarski(k2_relat_1(k7_relat_1(sK3,X4)),sK1)) ) | ~spl4_40),
% 0.21/0.50    inference(resolution,[],[f332,f184])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(resolution,[],[f82,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.50  fof(f16,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ( ! [X3] : (m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) ) | ~spl4_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f331])).
% 0.21/0.50  fof(f333,plain,(
% 0.21/0.50    ~spl4_9 | spl4_40 | ~spl4_7 | ~spl4_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f329,f274,f119,f331,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl4_9 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ( ! [X3] : (m1_subset_1(k7_relat_1(sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) ) | (~spl4_7 | ~spl4_32)),
% 0.21/0.50    inference(forward_demodulation,[],[f322,f275])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ( ! [X3] : (m1_subset_1(k2_partfun1(sK0,sK1,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) ) | ~spl4_7),
% 0.21/0.50    inference(resolution,[],[f91,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    ~spl4_9 | ~spl4_7 | spl4_36 | ~spl4_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f283,f274,f293,f119,f127])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_1(k7_relat_1(sK3,X0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3)) ) | ~spl4_32),
% 0.21/0.50    inference(superposition,[],[f90,f275])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f49])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    ~spl4_34 | spl4_2 | ~spl4_32),
% 0.21/0.50    inference(avatar_split_clause,[],[f281,f274,f101,f285])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    spl4_34 <=> v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.50  fof(f281,plain,(
% 0.21/0.50    ~v1_funct_2(k7_relat_1(sK3,sK2),sK2,sK1) | (spl4_2 | ~spl4_32)),
% 0.21/0.50    inference(superposition,[],[f102,f275])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    ~spl4_9 | spl4_32 | ~spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f267,f119,f274,f127])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    ( ! [X3] : (k2_partfun1(sK0,sK1,sK3,X3) = k7_relat_1(sK3,X3) | ~v1_funct_1(sK3)) ) | ~spl4_7),
% 0.21/0.50    inference(resolution,[],[f89,f120])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    ~spl4_9 | ~spl4_7 | spl4_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f247,f98,f119,f127])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl4_1 <=> v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | spl4_1),
% 0.21/0.50    inference(resolution,[],[f90,f99])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2)) | spl4_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ~spl4_7 | spl4_22),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f215])).
% 0.21/0.50  fof(f215,plain,(
% 0.21/0.50    $false | (~spl4_7 | spl4_22)),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f214])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_22),
% 0.21/0.50    inference(resolution,[],[f196,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl4_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f195])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    ~spl4_16 | spl4_24 | ~spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f201,f139,f203,f159])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    spl4_16 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    spl4_12 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl4_12),
% 0.21/0.50    inference(forward_demodulation,[],[f193,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f139])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    ( ! [X0] : (r1_tarski(k2_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.50    inference(resolution,[],[f184,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl4_18 | ~spl4_19 | ~spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f171,f115,f176,f173])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ~r1_xboole_0(sK2,sK0) | v1_xboole_0(sK2) | ~spl4_6),
% 0.21/0.50    inference(resolution,[],[f71,f116])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    spl4_16 | ~spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f153,f135,f159])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl4_11 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    v1_relat_1(k1_xboole_0) | ~spl4_11),
% 0.21/0.50    inference(superposition,[],[f66,f136])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f135])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl4_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f62,f143])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl4_13 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl4_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f63,f139])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    spl4_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f61,f135])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    spl4_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f60,f131])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl4_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f127])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    (~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK2,sK0) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((((~m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) | ~v1_funct_1(k2_partfun1(X0,X1,X3,X2))) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f23])).
% 0.21/0.50  fof(f23,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X2,X0) => ((m1_subset_1(k2_partfun1(X0,X1,X3,X2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(k2_partfun1(X0,X1,X3,X2),X2,X1) & v1_funct_1(k2_partfun1(X0,X1,X3,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl4_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f123])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl4_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f56,f119])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl4_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f57,f115])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    r1_tarski(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ~spl4_4 | spl4_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f58,f111,f108])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f59,f104,f101,f98])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ~m1_subset_1(k2_partfun1(sK0,sK1,sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_partfun1(sK0,sK1,sK3,sK2),sK2,sK1) | ~v1_funct_1(k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f51])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26041)------------------------------
% 0.21/0.50  % (26041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26041)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26041)Memory used [KB]: 11257
% 0.21/0.50  % (26041)Time elapsed: 0.076 s
% 0.21/0.50  % (26041)------------------------------
% 0.21/0.50  % (26041)------------------------------
% 0.21/0.50  % (26034)Success in time 0.141 s
%------------------------------------------------------------------------------
