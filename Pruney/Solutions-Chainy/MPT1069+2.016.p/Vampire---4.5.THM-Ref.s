%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 357 expanded)
%              Number of leaves         :   51 ( 180 expanded)
%              Depth                    :    8
%              Number of atoms          :  687 (1919 expanded)
%              Number of equality atoms :  106 ( 371 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f147,f179,f184,f190,f214,f221,f228,f253,f260,f261,f277,f308,f313,f319,f330,f331,f341,f348,f441,f489,f496])).

fof(f496,plain,
    ( spl6_42
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f495,f311,f145,f114,f110,f303])).

fof(f303,plain,
    ( spl6_42
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f110,plain,
    ( spl6_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f114,plain,
    ( spl6_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f145,plain,
    ( spl6_13
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f311,plain,
    ( spl6_44
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f495,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_xboole_0 = sK2
    | ~ spl6_13
    | ~ spl6_44 ),
    inference(resolution,[],[f312,f146])).

fof(f146,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f145])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | k1_xboole_0 = X0 )
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f311])).

fof(f489,plain,
    ( ~ spl6_7
    | spl6_10
    | spl6_45
    | ~ spl6_8
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f487,f346,f114,f317,f122,f110])).

fof(f122,plain,
    ( spl6_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f317,plain,
    ( spl6_45
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f346,plain,
    ( spl6_49
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f487,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_8
    | ~ spl6_49 ),
    inference(resolution,[],[f347,f115])).

fof(f115,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f346])).

fof(f441,plain,
    ( spl6_2
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f433,f317,f90])).

fof(f90,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f433,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_45 ),
    inference(resolution,[],[f318,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f318,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f317])).

fof(f348,plain,
    ( ~ spl6_9
    | spl6_49
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f342,f339,f346,f118])).

fof(f118,plain,
    ( spl6_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f339,plain,
    ( spl6_48
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f342,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK3,X0,X1)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl6_48 ),
    inference(resolution,[],[f340,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f340,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f339])).

fof(f341,plain,
    ( spl6_48
    | ~ spl6_11
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f333,f328,f126,f339])).

fof(f126,plain,
    ( spl6_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f328,plain,
    ( spl6_46
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f333,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_11
    | ~ spl6_46 ),
    inference(resolution,[],[f329,f139])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl6_11 ),
    inference(resolution,[],[f60,f127])).

fof(f127,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f329,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f328])).

fof(f331,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f330,plain,
    ( ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | spl6_46
    | spl6_42
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f326,f275,f303,f328,f110,f114,f118])).

fof(f275,plain,
    ( spl6_36
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f326,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ spl6_36 ),
    inference(resolution,[],[f276,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relset_1(X0,X2,X1),k1_xboole_0)
      | k1_xboole_0 = X2
      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_2(X1,X0,X2)
      | ~ v1_funct_1(X1) ) ),
    inference(superposition,[],[f78,f80])).

% (1871)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f276,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f275])).

fof(f319,plain,
    ( ~ spl6_4
    | spl6_45
    | spl6_43 ),
    inference(avatar_split_clause,[],[f314,f306,f317,f98])).

fof(f98,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f306,plain,
    ( spl6_43
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f314,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK5,sK1)
    | spl6_43 ),
    inference(resolution,[],[f307,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f307,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl6_43 ),
    inference(avatar_component_clause,[],[f306])).

fof(f313,plain,
    ( ~ spl6_9
    | spl6_44
    | spl6_41 ),
    inference(avatar_split_clause,[],[f309,f300,f311,f118])).

fof(f300,plain,
    ( spl6_41
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f309,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(sK3,sK1,X0)
        | ~ v1_funct_1(sK3) )
    | spl6_41 ),
    inference(resolution,[],[f301,f78])).

fof(f301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f300])).

fof(f308,plain,
    ( ~ spl6_41
    | spl6_42
    | ~ spl6_43
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_13
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f298,f258,f145,f114,f110,f306,f303,f300])).

fof(f258,plain,
    ( spl6_33
  <=> ! [X1,X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r1_tarski(k2_relset_1(X0,X1,sK3),k1_relat_1(sK4))
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f298,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ r2_hidden(sK5,sK1)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl6_13
    | ~ spl6_33 ),
    inference(resolution,[],[f259,f146])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k2_relset_1(X0,X1,sK3),k1_relat_1(sK4))
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ r2_hidden(sK5,X0)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f277,plain,
    ( spl6_36
    | ~ spl6_13
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f264,f235,f145,f275])).

fof(f235,plain,
    ( spl6_29
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f264,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_29 ),
    inference(superposition,[],[f146,f236])).

fof(f236,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f235])).

fof(f261,plain,
    ( ~ spl6_9
    | spl6_28
    | spl6_29
    | spl6_25 ),
    inference(avatar_split_clause,[],[f254,f212,f235,f232,f118])).

fof(f232,plain,
    ( spl6_28
  <=> ! [X0] :
        ( ~ r2_hidden(sK5,X0)
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f212,plain,
    ( spl6_25
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f254,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK4)
        | ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ v1_funct_1(sK3) )
    | spl6_25 ),
    inference(resolution,[],[f213,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

fof(f213,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f212])).

fof(f260,plain,
    ( ~ spl6_9
    | spl6_33
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f256,f232,f258,f118])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))
        | k1_xboole_0 = X1
        | ~ r1_tarski(k2_relset_1(X0,X1,sK3),k1_relat_1(sK4))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ v1_funct_1(sK3) )
    | ~ spl6_28 ),
    inference(resolution,[],[f233,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,X0,k1_relat_1(sK4))
        | ~ r2_hidden(sK5,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f232])).

fof(f253,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl6_26 ),
    inference(resolution,[],[f220,f61])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f220,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl6_26
  <=> v1_relat_1(k2_zfmisc_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f228,plain,
    ( ~ spl6_5
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl6_5
    | spl6_24 ),
    inference(subsumption_resolution,[],[f103,f226])).

fof(f226,plain,
    ( ! [X0] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_24 ),
    inference(resolution,[],[f210,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f210,plain,
    ( ~ v5_relat_1(sK4,sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl6_24
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f103,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f221,plain,
    ( ~ spl6_26
    | ~ spl6_5
    | spl6_23 ),
    inference(avatar_split_clause,[],[f216,f206,f102,f219])).

fof(f206,plain,
    ( spl6_23
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f216,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl6_5
    | spl6_23 ),
    inference(resolution,[],[f215,f103])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_23 ),
    inference(resolution,[],[f207,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f207,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f214,plain,
    ( ~ spl6_23
    | ~ spl6_24
    | ~ spl6_6
    | ~ spl6_25
    | spl6_19 ),
    inference(avatar_split_clause,[],[f204,f188,f212,f106,f209,f206])).

fof(f106,plain,
    ( spl6_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f188,plain,
    ( spl6_19
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f204,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl6_19 ),
    inference(trivial_inequality_removal,[],[f203])).

fof(f203,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v5_relat_1(sK4,sK0)
    | ~ v1_relat_1(sK4)
    | spl6_19 ),
    inference(superposition,[],[f189,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f189,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_19 ),
    inference(avatar_component_clause,[],[f188])).

fof(f190,plain,
    ( ~ spl6_19
    | spl6_1
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f185,f182,f86,f188])).

fof(f86,plain,
    ( spl6_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f182,plain,
    ( spl6_18
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f185,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_18 ),
    inference(superposition,[],[f87,f183])).

fof(f183,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f182])).

fof(f87,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f184,plain,
    ( spl6_18
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f180,f176,f98,f182])).

fof(f176,plain,
    ( spl6_17
  <=> ! [X0] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f180,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(resolution,[],[f177,f99])).

fof(f99,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f179,plain,
    ( spl6_10
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | spl6_17
    | spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f167,f94,f90,f176,f102,f106,f110,f114,f118,f122])).

fof(f94,plain,
    ( spl6_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f167,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | ~ spl6_3 ),
    inference(resolution,[],[f70,f95])).

fof(f95,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f147,plain,
    ( ~ spl6_5
    | spl6_13
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f142,f94,f145,f102])).

fof(f142,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_3 ),
    inference(superposition,[],[f95,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f128,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f56,f126])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f124,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f46,f122])).

fof(f46,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f42,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f19])).

% (1856)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f120,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f47,f118])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f116,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f48,f114])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f112,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f49,f110])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f50,f106])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f104,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f51,f102])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f100,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f98])).

fof(f52,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f96,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f53,f94])).

fof(f53,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f54,f90])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f55,f86])).

fof(f55,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (1869)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (1861)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (1860)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1858)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (1858)Refutation not found, incomplete strategy% (1858)------------------------------
% 0.21/0.50  % (1858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1858)Memory used [KB]: 10746
% 0.21/0.50  % (1858)Time elapsed: 0.082 s
% 0.21/0.50  % (1858)------------------------------
% 0.21/0.50  % (1858)------------------------------
% 0.21/0.50  % (1863)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (1857)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (1874)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (1861)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f497,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f108,f112,f116,f120,f124,f128,f147,f179,f184,f190,f214,f221,f228,f253,f260,f261,f277,f308,f313,f319,f330,f331,f341,f348,f441,f489,f496])).
% 0.21/0.51  fof(f496,plain,(
% 0.21/0.51    spl6_42 | ~spl6_7 | ~spl6_8 | ~spl6_13 | ~spl6_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f495,f311,f145,f114,f110,f303])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    spl6_42 <=> k1_xboole_0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl6_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    spl6_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl6_13 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    spl6_44 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_xboole_0 = sK2 | (~spl6_13 | ~spl6_44)),
% 0.21/0.51    inference(resolution,[],[f312,f146])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f145])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | ~v1_funct_2(sK3,sK1,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | k1_xboole_0 = X0) ) | ~spl6_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f311])).
% 0.21/0.51  fof(f489,plain,(
% 0.21/0.51    ~spl6_7 | spl6_10 | spl6_45 | ~spl6_8 | ~spl6_49),
% 0.21/0.51    inference(avatar_split_clause,[],[f487,f346,f114,f317,f122,f110])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    spl6_10 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    spl6_45 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    spl6_49 <=> ! [X1,X0] : (~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.21/0.51  fof(f487,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_8 | ~spl6_49)),
% 0.21/0.51    inference(resolution,[],[f347,f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2) | ~spl6_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f114])).
% 0.21/0.51  fof(f347,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_2(sK3,X0,X1) | v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f346])).
% 0.21/0.51  fof(f441,plain,(
% 0.21/0.51    spl6_2 | ~spl6_45),
% 0.21/0.51    inference(avatar_split_clause,[],[f433,f317,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl6_2 <=> k1_xboole_0 = sK1),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | ~spl6_45),
% 0.21/0.51    inference(resolution,[],[f318,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~spl6_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f317])).
% 0.21/0.51  fof(f348,plain,(
% 0.21/0.51    ~spl6_9 | spl6_49 | ~spl6_48),
% 0.21/0.51    inference(avatar_split_clause,[],[f342,f339,f346,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl6_9 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    spl6_48 <=> v1_xboole_0(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.21/0.51  fof(f342,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) ) | ~spl6_48),
% 0.21/0.51    inference(resolution,[],[f340,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_funct_2)).
% 0.21/0.51  fof(f340,plain,(
% 0.21/0.51    v1_xboole_0(sK3) | ~spl6_48),
% 0.21/0.51    inference(avatar_component_clause,[],[f339])).
% 0.21/0.51  fof(f341,plain,(
% 0.21/0.51    spl6_48 | ~spl6_11 | ~spl6_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f333,f328,f126,f339])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl6_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    spl6_46 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    v1_xboole_0(sK3) | (~spl6_11 | ~spl6_46)),
% 0.21/0.51    inference(resolution,[],[f329,f139])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl6_11),
% 0.21/0.51    inference(resolution,[],[f60,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0) | ~spl6_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f328])).
% 0.21/0.51  fof(f331,plain,(
% 0.21/0.51    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f330,plain,(
% 0.21/0.51    ~spl6_9 | ~spl6_8 | ~spl6_7 | spl6_46 | spl6_42 | ~spl6_36),
% 0.21/0.51    inference(avatar_split_clause,[],[f326,f275,f303,f328,f110,f114,f118])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    spl6_36 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~spl6_36),
% 0.21/0.51    inference(resolution,[],[f276,f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(X0,X2,X1),k1_xboole_0) | k1_xboole_0 = X2 | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X1,X0,X2) | ~v1_funct_1(X1)) )),
% 0.21/0.51    inference(superposition,[],[f78,f80])).
% 0.21/0.51  % (1871)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(equality_resolution,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(flattening,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | ~spl6_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f275])).
% 0.21/0.51  fof(f319,plain,(
% 0.21/0.51    ~spl6_4 | spl6_45 | spl6_43),
% 0.21/0.51    inference(avatar_split_clause,[],[f314,f306,f317,f98])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl6_4 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    spl6_43 <=> r2_hidden(sK5,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~m1_subset_1(sK5,sK1) | spl6_43),
% 0.21/0.51    inference(resolution,[],[f307,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    ~r2_hidden(sK5,sK1) | spl6_43),
% 0.21/0.51    inference(avatar_component_clause,[],[f306])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    ~spl6_9 | spl6_44 | spl6_41),
% 0.21/0.51    inference(avatar_split_clause,[],[f309,f300,f311,f118])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    spl6_41 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(k2_relset_1(sK1,X0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(sK3,sK1,X0) | ~v1_funct_1(sK3)) ) | spl6_41),
% 0.21/0.51    inference(resolution,[],[f301,f78])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | spl6_41),
% 0.21/0.51    inference(avatar_component_clause,[],[f300])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    ~spl6_41 | spl6_42 | ~spl6_43 | ~spl6_7 | ~spl6_8 | ~spl6_13 | ~spl6_33),
% 0.21/0.51    inference(avatar_split_clause,[],[f298,f258,f145,f114,f110,f306,f303,f300])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    spl6_33 <=> ! [X1,X0] : (~r2_hidden(sK5,X0) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,sK3),k1_relat_1(sK4)) | k1_xboole_0 = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~r2_hidden(sK5,sK1) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | (~spl6_13 | ~spl6_33)),
% 0.21/0.51    inference(resolution,[],[f259,f146])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relset_1(X0,X1,sK3),k1_relat_1(sK4)) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(sK5,X0) | k1_xboole_0 = X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))) ) | ~spl6_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f258])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    spl6_36 | ~spl6_13 | ~spl6_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f264,f235,f145,f275])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    spl6_29 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_xboole_0) | (~spl6_13 | ~spl6_29)),
% 0.21/0.51    inference(superposition,[],[f146,f236])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(sK4) | ~spl6_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f235])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    ~spl6_9 | spl6_28 | spl6_29 | spl6_25),
% 0.21/0.51    inference(avatar_split_clause,[],[f254,f212,f235,f232,f118])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    spl6_28 <=> ! [X0] : (~r2_hidden(sK5,X0) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl6_25 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK4) | ~r2_hidden(sK5,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | ~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~v1_funct_1(sK3)) ) | spl6_25),
% 0.21/0.51    inference(resolution,[],[f213,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl6_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f212])).
% 0.21/0.51  fof(f260,plain,(
% 0.21/0.51    ~spl6_9 | spl6_33 | ~spl6_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f256,f232,f258,f118])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK5,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4)))) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) ) | ~spl6_28),
% 0.21/0.51    inference(resolution,[],[f233,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK3,X0,k1_relat_1(sK4)) | ~r2_hidden(sK5,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_relat_1(sK4))))) ) | ~spl6_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f232])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl6_26),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    $false | spl6_26),
% 0.21/0.51    inference(resolution,[],[f220,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | spl6_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f219])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl6_26 <=> v1_relat_1(k2_zfmisc_1(sK2,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.51  fof(f228,plain,(
% 0.21/0.51    ~spl6_5 | spl6_24),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f227])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    $false | (~spl6_5 | spl6_24)),
% 0.21/0.51    inference(subsumption_resolution,[],[f103,f226])).
% 0.21/0.51  fof(f226,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl6_24),
% 0.21/0.51    inference(resolution,[],[f210,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~v5_relat_1(sK4,sK0) | spl6_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl6_24 <=> v5_relat_1(sK4,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    spl6_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ~spl6_26 | ~spl6_5 | spl6_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f216,f206,f102,f219])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    spl6_23 <=> v1_relat_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.51  fof(f216,plain,(
% 0.21/0.51    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | (~spl6_5 | spl6_23)),
% 0.21/0.51    inference(resolution,[],[f215,f103])).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK4,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_23),
% 0.21/0.51    inference(resolution,[],[f207,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ~v1_relat_1(sK4) | spl6_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f206])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ~spl6_23 | ~spl6_24 | ~spl6_6 | ~spl6_25 | spl6_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f204,f188,f212,f106,f209,f206])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl6_6 <=> v1_funct_1(sK4)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl6_19 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl6_19),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f203])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~v1_funct_1(sK4) | ~v5_relat_1(sK4,sK0) | ~v1_relat_1(sK4) | spl6_19),
% 0.21/0.51    inference(superposition,[],[f189,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f188])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    ~spl6_19 | spl6_1 | ~spl6_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f185,f182,f86,f188])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl6_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    spl6_18 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_18)),
% 0.21/0.51    inference(superposition,[],[f87,f183])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl6_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f182])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl6_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f86])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    spl6_18 | ~spl6_4 | ~spl6_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f180,f176,f98,f182])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl6_17 <=> ! [X0] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl6_4 | ~spl6_17)),
% 0.21/0.51    inference(resolution,[],[f177,f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f98])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0))) ) | ~spl6_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f176])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl6_10 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | spl6_17 | spl6_2 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f94,f90,f176,f102,f106,f110,f114,f118,f122])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    spl6_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X0) = k1_funct_1(sK4,k1_funct_1(sK3,X0)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) ) | ~spl6_3),
% 0.21/0.51    inference(resolution,[],[f70,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f94])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ~spl6_5 | spl6_13 | ~spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f142,f94,f145,f102])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_3),
% 0.21/0.51    inference(superposition,[],[f95,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    spl6_11),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f126])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~spl6_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f122])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f42,f41,f40,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  % (1856)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f16])).
% 0.21/0.51  fof(f16,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    spl6_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f118])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl6_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f114])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl6_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f110])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl6_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f106])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_funct_1(sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl6_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f102])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f98])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    m1_subset_1(sK5,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl6_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f94])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~spl6_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f54,f90])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ~spl6_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f55,f86])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (1861)------------------------------
% 0.21/0.51  % (1861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1861)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (1861)Memory used [KB]: 11001
% 0.21/0.51  % (1861)Time elapsed: 0.034 s
% 0.21/0.51  % (1861)------------------------------
% 0.21/0.51  % (1861)------------------------------
% 0.21/0.51  % (1875)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (1859)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (1855)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (1852)Success in time 0.154 s
%------------------------------------------------------------------------------
