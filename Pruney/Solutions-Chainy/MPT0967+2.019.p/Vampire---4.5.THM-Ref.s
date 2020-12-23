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
% DateTime   : Thu Dec  3 13:00:45 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 287 expanded)
%              Number of leaves         :   37 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  497 (1184 expanded)
%              Number of equality atoms :   86 ( 235 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f79,f83,f87,f91,f93,f104,f112,f115,f136,f152,f194,f241,f242,f252,f268,f274,f279,f322,f328,f329,f363,f427,f430,f431])).

fof(f431,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k1_relat_1(sK3)
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f430,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != sK3
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f427,plain,
    ( ~ spl5_38
    | spl5_41
    | ~ spl5_4
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f422,f250,f144,f74,f425,f361])).

fof(f361,plain,
    ( spl5_38
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f425,plain,
    ( spl5_41
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f74,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f144,plain,
    ( spl5_14
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f250,plain,
    ( spl5_25
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f422,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f421,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f421,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f420,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f420,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_4
    | ~ spl5_14
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f419,f145])).

fof(f419,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_4
    | ~ spl5_25 ),
    inference(forward_demodulation,[],[f412,f239])).

fof(f412,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK1)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3)
    | ~ spl5_25 ),
    inference(resolution,[],[f251,f62])).

fof(f62,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f251,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f250])).

fof(f363,plain,
    ( spl5_38
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f359,f144,f89,f77,f74,f361])).

fof(f77,plain,
    ( spl5_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f89,plain,
    ( spl5_8
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f359,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f358,f145])).

fof(f358,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f349,f78])).

fof(f78,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f349,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl5_4
    | ~ spl5_8 ),
    inference(superposition,[],[f90,f239])).

fof(f90,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f329,plain,
    ( ~ spl5_30
    | spl5_3
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f306,f265,f134,f70,f277])).

fof(f277,plain,
    ( spl5_30
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f70,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f134,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f265,plain,
    ( spl5_28
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f306,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_3
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(resolution,[],[f71,f269])).

fof(f269,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(superposition,[],[f135,f266])).

fof(f266,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f265])).

fof(f135,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ r1_tarski(k2_relat_1(sK3),X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f71,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f328,plain,
    ( ~ spl5_6
    | ~ spl5_11
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f323,f320,f110,f81])).

fof(f81,plain,
    ( spl5_6
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( spl5_11
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f320,plain,
    ( spl5_34
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(k2_relat_1(sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f323,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_11
    | ~ spl5_34 ),
    inference(resolution,[],[f321,f111])).

fof(f111,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f110])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f320])).

fof(f322,plain,
    ( spl5_30
    | spl5_34
    | spl5_30 ),
    inference(avatar_split_clause,[],[f316,f277,f320,f277])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(k2_relat_1(sK3),X0)
        | r1_tarski(k2_relat_1(sK3),sK2) )
    | spl5_30 ),
    inference(resolution,[],[f282,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f282,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),X1)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,X0) )
    | spl5_30 ),
    inference(resolution,[],[f280,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(k2_relat_1(sK3),sK2),X0)
        | ~ r1_tarski(X0,sK2) )
    | spl5_30 ),
    inference(resolution,[],[f278,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r2_hidden(sK4(X0,X1),X2) ) ),
    inference(resolution,[],[f46,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f278,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( ~ spl5_30
    | spl5_2
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f275,f272,f67,f277])).

fof(f67,plain,
    ( spl5_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f272,plain,
    ( spl5_29
  <=> ! [X1] :
        ( v1_funct_2(sK3,sK0,X1)
        | ~ r1_tarski(k2_relat_1(sK3),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f275,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | spl5_2
    | ~ spl5_29 ),
    inference(resolution,[],[f273,f68])).

fof(f68,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f273,plain,
    ( ! [X1] :
        ( v1_funct_2(sK3,sK0,X1)
        | ~ r1_tarski(k2_relat_1(sK3),X1) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f272])).

fof(f274,plain,
    ( ~ spl5_10
    | ~ spl5_1
    | spl5_29
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f270,f265,f272,f64,f107])).

fof(f107,plain,
    ( spl5_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f64,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f270,plain,
    ( ! [X1] :
        ( v1_funct_2(sK3,sK0,X1)
        | ~ r1_tarski(k2_relat_1(sK3),X1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_28 ),
    inference(superposition,[],[f44,f266])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f268,plain,
    ( ~ spl5_7
    | spl5_28
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f262,f237,f265,f85])).

fof(f85,plain,
    ( spl5_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f237,plain,
    ( spl5_23
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f262,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_23 ),
    inference(superposition,[],[f50,f238])).

fof(f238,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f237])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f252,plain,
    ( spl5_25
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f246,f85,f77,f250])).

fof(f246,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(superposition,[],[f86,f78])).

fof(f86,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f242,plain,
    ( k1_xboole_0 != sK1
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f241,plain,
    ( spl5_23
    | spl5_4
    | ~ spl5_8
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f234,f85,f89,f74,f237])).

fof(f234,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl5_7 ),
    inference(resolution,[],[f52,f86])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f194,plain,
    ( ~ spl5_10
    | ~ spl5_1
    | ~ spl5_13
    | spl5_16 ),
    inference(avatar_split_clause,[],[f172,f150,f141,f64,f107])).

fof(f141,plain,
    ( spl5_13
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f150,plain,
    ( spl5_16
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f172,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl5_16 ),
    inference(resolution,[],[f151,f44])).

fof(f151,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( ~ spl5_13
    | spl5_14
    | spl5_15
    | ~ spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f139,f134,f150,f147,f144,f141])).

fof(f147,plain,
    ( spl5_15
  <=> k1_xboole_0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f139,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl5_12 ),
    inference(resolution,[],[f60,f135])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f136,plain,
    ( ~ spl5_10
    | spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f132,f64,f134,f107])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f92])).

fof(f92,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,
    ( ~ spl5_7
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl5_7
    | spl5_10 ),
    inference(subsumption_resolution,[],[f86,f113])).

fof(f113,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_10 ),
    inference(resolution,[],[f108,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f108,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f112,plain,
    ( ~ spl5_10
    | spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f105,f102,f110,f107])).

fof(f102,plain,
    ( spl5_9
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f105,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl5_9 ),
    inference(resolution,[],[f103,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f103,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f104,plain,
    ( spl5_9
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f100,f85,f102])).

fof(f100,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f51,f86])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f93,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f33,f64])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).

% (20491)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

% (20492)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

% (20489)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (20503)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f91,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f35,f85])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f37,f77,f74])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f38,f70,f67,f64])).

fof(f38,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:52:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (20479)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.51  % (20478)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (20477)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (20479)Refutation not found, incomplete strategy% (20479)------------------------------
% 0.22/0.51  % (20479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (20474)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (20475)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (20494)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (20486)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (20479)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20479)Memory used [KB]: 6268
% 0.22/0.52  % (20479)Time elapsed: 0.098 s
% 0.22/0.52  % (20479)------------------------------
% 0.22/0.52  % (20479)------------------------------
% 0.22/0.52  % (20493)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (20496)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (20480)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (20496)Refutation not found, incomplete strategy% (20496)------------------------------
% 0.22/0.53  % (20496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20496)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20496)Memory used [KB]: 10874
% 0.22/0.53  % (20496)Time elapsed: 0.108 s
% 0.22/0.53  % (20496)------------------------------
% 0.22/0.53  % (20496)------------------------------
% 0.22/0.53  % (20497)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (20476)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (20494)Refutation not found, incomplete strategy% (20494)------------------------------
% 1.28/0.53  % (20494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (20494)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (20494)Memory used [KB]: 10874
% 1.28/0.53  % (20494)Time elapsed: 0.116 s
% 1.28/0.53  % (20494)------------------------------
% 1.28/0.53  % (20494)------------------------------
% 1.28/0.53  % (20485)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.53  % (20487)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.28/0.53  % (20485)Refutation not found, incomplete strategy% (20485)------------------------------
% 1.28/0.53  % (20485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (20485)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (20485)Memory used [KB]: 10618
% 1.28/0.53  % (20485)Time elapsed: 0.120 s
% 1.28/0.53  % (20485)------------------------------
% 1.28/0.53  % (20485)------------------------------
% 1.28/0.53  % (20498)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.28/0.53  % (20476)Refutation not found, incomplete strategy% (20476)------------------------------
% 1.28/0.53  % (20476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.53  % (20476)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.53  
% 1.28/0.53  % (20476)Memory used [KB]: 10746
% 1.28/0.53  % (20476)Time elapsed: 0.114 s
% 1.28/0.53  % (20476)------------------------------
% 1.28/0.53  % (20476)------------------------------
% 1.28/0.53  % (20481)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.28/0.54  % (20478)Refutation not found, incomplete strategy% (20478)------------------------------
% 1.28/0.54  % (20478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (20484)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.28/0.54  % (20488)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.28/0.54  % (20478)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (20478)Memory used [KB]: 6268
% 1.28/0.54  % (20478)Time elapsed: 0.128 s
% 1.28/0.54  % (20478)------------------------------
% 1.28/0.54  % (20478)------------------------------
% 1.28/0.54  % (20499)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.28/0.54  % (20500)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.28/0.54  % (20495)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.28/0.54  % (20493)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f432,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(avatar_sat_refutation,[],[f72,f79,f83,f87,f91,f93,f104,f112,f115,f136,f152,f194,f241,f242,f252,f268,f274,f279,f322,f328,f329,f363,f427,f430,f431])).
% 1.28/0.54  fof(f431,plain,(
% 1.28/0.54    k1_xboole_0 != sK0 | k1_xboole_0 != k1_relat_1(sK3) | sK0 = k1_relat_1(sK3)),
% 1.28/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.54  fof(f430,plain,(
% 1.28/0.54    k1_xboole_0 != sK1 | k1_xboole_0 != sK3 | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.28/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.54  fof(f427,plain,(
% 1.28/0.54    ~spl5_38 | spl5_41 | ~spl5_4 | ~spl5_14 | ~spl5_25),
% 1.28/0.54    inference(avatar_split_clause,[],[f422,f250,f144,f74,f425,f361])).
% 1.28/0.54  fof(f361,plain,(
% 1.28/0.54    spl5_38 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.28/0.54  fof(f425,plain,(
% 1.28/0.54    spl5_41 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.28/0.54  fof(f74,plain,(
% 1.28/0.54    spl5_4 <=> k1_xboole_0 = sK1),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.28/0.54  fof(f144,plain,(
% 1.28/0.54    spl5_14 <=> k1_xboole_0 = sK3),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.28/0.54  fof(f250,plain,(
% 1.28/0.54    spl5_25 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.28/0.54  fof(f422,plain,(
% 1.28/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_14 | ~spl5_25)),
% 1.28/0.54    inference(forward_demodulation,[],[f421,f239])).
% 1.28/0.54  fof(f239,plain,(
% 1.28/0.54    k1_xboole_0 = sK1 | ~spl5_4),
% 1.28/0.54    inference(avatar_component_clause,[],[f74])).
% 1.28/0.54  fof(f421,plain,(
% 1.28/0.54    k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_14 | ~spl5_25)),
% 1.28/0.54    inference(forward_demodulation,[],[f420,f145])).
% 1.28/0.54  fof(f145,plain,(
% 1.28/0.54    k1_xboole_0 = sK3 | ~spl5_14),
% 1.28/0.54    inference(avatar_component_clause,[],[f144])).
% 1.28/0.54  fof(f420,plain,(
% 1.28/0.54    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl5_4 | ~spl5_14 | ~spl5_25)),
% 1.28/0.54    inference(forward_demodulation,[],[f419,f145])).
% 1.28/0.54  fof(f419,plain,(
% 1.28/0.54    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | (~spl5_4 | ~spl5_25)),
% 1.28/0.54    inference(forward_demodulation,[],[f412,f239])).
% 1.28/0.54  fof(f412,plain,(
% 1.28/0.54    ~v1_funct_2(sK3,k1_xboole_0,sK1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK1,sK3) | ~spl5_25),
% 1.28/0.54    inference(resolution,[],[f251,f62])).
% 1.28/0.54  fof(f62,plain,(
% 1.28/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.28/0.54    inference(equality_resolution,[],[f53])).
% 1.28/0.54  fof(f53,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f32])).
% 1.28/0.54  fof(f32,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(nnf_transformation,[],[f24])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(flattening,[],[f23])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.28/0.54  fof(f251,plain,(
% 1.28/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_25),
% 1.28/0.54    inference(avatar_component_clause,[],[f250])).
% 1.28/0.54  fof(f363,plain,(
% 1.28/0.54    spl5_38 | ~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14),
% 1.28/0.54    inference(avatar_split_clause,[],[f359,f144,f89,f77,f74,f361])).
% 1.28/0.54  fof(f77,plain,(
% 1.28/0.54    spl5_5 <=> k1_xboole_0 = sK0),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.28/0.54  fof(f89,plain,(
% 1.28/0.54    spl5_8 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.28/0.54  fof(f359,plain,(
% 1.28/0.54    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5 | ~spl5_8 | ~spl5_14)),
% 1.28/0.54    inference(forward_demodulation,[],[f358,f145])).
% 1.28/0.54  fof(f358,plain,(
% 1.28/0.54    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl5_4 | ~spl5_5 | ~spl5_8)),
% 1.28/0.54    inference(forward_demodulation,[],[f349,f78])).
% 1.28/0.54  fof(f78,plain,(
% 1.28/0.54    k1_xboole_0 = sK0 | ~spl5_5),
% 1.28/0.54    inference(avatar_component_clause,[],[f77])).
% 1.28/0.54  fof(f349,plain,(
% 1.28/0.54    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl5_4 | ~spl5_8)),
% 1.28/0.54    inference(superposition,[],[f90,f239])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    v1_funct_2(sK3,sK0,sK1) | ~spl5_8),
% 1.28/0.54    inference(avatar_component_clause,[],[f89])).
% 1.28/0.54  fof(f329,plain,(
% 1.28/0.54    ~spl5_30 | spl5_3 | ~spl5_12 | ~spl5_28),
% 1.28/0.54    inference(avatar_split_clause,[],[f306,f265,f134,f70,f277])).
% 1.28/0.54  fof(f277,plain,(
% 1.28/0.54    spl5_30 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.28/0.54  fof(f70,plain,(
% 1.28/0.54    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.28/0.54  fof(f134,plain,(
% 1.28/0.54    spl5_12 <=> ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.28/0.54  fof(f265,plain,(
% 1.28/0.54    spl5_28 <=> sK0 = k1_relat_1(sK3)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.28/0.54  fof(f306,plain,(
% 1.28/0.54    ~r1_tarski(k2_relat_1(sK3),sK2) | (spl5_3 | ~spl5_12 | ~spl5_28)),
% 1.28/0.54    inference(resolution,[],[f71,f269])).
% 1.28/0.54  fof(f269,plain,(
% 1.28/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(k2_relat_1(sK3),X0)) ) | (~spl5_12 | ~spl5_28)),
% 1.28/0.54    inference(superposition,[],[f135,f266])).
% 1.28/0.54  fof(f266,plain,(
% 1.28/0.54    sK0 = k1_relat_1(sK3) | ~spl5_28),
% 1.28/0.54    inference(avatar_component_clause,[],[f265])).
% 1.28/0.54  fof(f135,plain,(
% 1.28/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~r1_tarski(k2_relat_1(sK3),X0)) ) | ~spl5_12),
% 1.28/0.54    inference(avatar_component_clause,[],[f134])).
% 1.28/0.54  fof(f71,plain,(
% 1.28/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl5_3),
% 1.28/0.54    inference(avatar_component_clause,[],[f70])).
% 1.28/0.54  fof(f328,plain,(
% 1.28/0.54    ~spl5_6 | ~spl5_11 | ~spl5_34),
% 1.28/0.54    inference(avatar_split_clause,[],[f323,f320,f110,f81])).
% 1.28/0.54  fof(f81,plain,(
% 1.28/0.54    spl5_6 <=> r1_tarski(sK1,sK2)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.28/0.54  fof(f110,plain,(
% 1.28/0.54    spl5_11 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.28/0.54  fof(f320,plain,(
% 1.28/0.54    spl5_34 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(k2_relat_1(sK3),X0))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.28/0.54  fof(f323,plain,(
% 1.28/0.54    ~r1_tarski(sK1,sK2) | (~spl5_11 | ~spl5_34)),
% 1.28/0.54    inference(resolution,[],[f321,f111])).
% 1.28/0.54  fof(f111,plain,(
% 1.28/0.54    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_11),
% 1.28/0.54    inference(avatar_component_clause,[],[f110])).
% 1.28/0.54  fof(f321,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | ~r1_tarski(X0,sK2)) ) | ~spl5_34),
% 1.28/0.54    inference(avatar_component_clause,[],[f320])).
% 1.28/0.54  fof(f322,plain,(
% 1.28/0.54    spl5_30 | spl5_34 | spl5_30),
% 1.28/0.54    inference(avatar_split_clause,[],[f316,f277,f320,f277])).
% 1.28/0.54  fof(f316,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(k2_relat_1(sK3),X0) | r1_tarski(k2_relat_1(sK3),sK2)) ) | spl5_30),
% 1.28/0.54    inference(resolution,[],[f282,f47])).
% 1.28/0.54  fof(f47,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f31])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(rectify,[],[f28])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.54    inference(nnf_transformation,[],[f19])).
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.54  fof(f282,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(k2_relat_1(sK3),sK2),X1) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,X0)) ) | spl5_30),
% 1.28/0.54    inference(resolution,[],[f280,f46])).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f31])).
% 1.28/0.54  fof(f280,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(sK4(k2_relat_1(sK3),sK2),X0) | ~r1_tarski(X0,sK2)) ) | spl5_30),
% 1.28/0.54    inference(resolution,[],[f278,f99])).
% 1.28/0.54  fof(f99,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | ~r2_hidden(sK4(X0,X1),X2)) )),
% 1.28/0.54    inference(resolution,[],[f46,f48])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f31])).
% 1.28/0.54  fof(f278,plain,(
% 1.28/0.54    ~r1_tarski(k2_relat_1(sK3),sK2) | spl5_30),
% 1.28/0.54    inference(avatar_component_clause,[],[f277])).
% 1.28/0.54  fof(f279,plain,(
% 1.28/0.54    ~spl5_30 | spl5_2 | ~spl5_29),
% 1.28/0.54    inference(avatar_split_clause,[],[f275,f272,f67,f277])).
% 1.28/0.54  fof(f67,plain,(
% 1.28/0.54    spl5_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.28/0.54  fof(f272,plain,(
% 1.28/0.54    spl5_29 <=> ! [X1] : (v1_funct_2(sK3,sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X1))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.28/0.54  fof(f275,plain,(
% 1.28/0.54    ~r1_tarski(k2_relat_1(sK3),sK2) | (spl5_2 | ~spl5_29)),
% 1.28/0.54    inference(resolution,[],[f273,f68])).
% 1.28/0.54  fof(f68,plain,(
% 1.28/0.54    ~v1_funct_2(sK3,sK0,sK2) | spl5_2),
% 1.28/0.54    inference(avatar_component_clause,[],[f67])).
% 1.28/0.54  fof(f273,plain,(
% 1.28/0.54    ( ! [X1] : (v1_funct_2(sK3,sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X1)) ) | ~spl5_29),
% 1.28/0.54    inference(avatar_component_clause,[],[f272])).
% 1.28/0.54  fof(f274,plain,(
% 1.28/0.54    ~spl5_10 | ~spl5_1 | spl5_29 | ~spl5_28),
% 1.28/0.54    inference(avatar_split_clause,[],[f270,f265,f272,f64,f107])).
% 1.28/0.54  fof(f107,plain,(
% 1.28/0.54    spl5_10 <=> v1_relat_1(sK3)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.28/0.54  fof(f64,plain,(
% 1.28/0.54    spl5_1 <=> v1_funct_1(sK3)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.28/0.54  fof(f270,plain,(
% 1.28/0.54    ( ! [X1] : (v1_funct_2(sK3,sK0,X1) | ~r1_tarski(k2_relat_1(sK3),X1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_28),
% 1.28/0.54    inference(superposition,[],[f44,f266])).
% 1.28/0.54  fof(f44,plain,(
% 1.28/0.54    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f18])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(flattening,[],[f17])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.28/0.54    inference(ennf_transformation,[],[f9])).
% 1.28/0.54  fof(f9,axiom,(
% 1.28/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.28/0.54  fof(f268,plain,(
% 1.28/0.54    ~spl5_7 | spl5_28 | ~spl5_23),
% 1.28/0.54    inference(avatar_split_clause,[],[f262,f237,f265,f85])).
% 1.28/0.54  fof(f85,plain,(
% 1.28/0.54    spl5_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.28/0.54  fof(f237,plain,(
% 1.28/0.54    spl5_23 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.28/0.54  fof(f262,plain,(
% 1.28/0.54    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_23),
% 1.28/0.54    inference(superposition,[],[f50,f238])).
% 1.28/0.54  fof(f238,plain,(
% 1.28/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_23),
% 1.28/0.54    inference(avatar_component_clause,[],[f237])).
% 1.28/0.54  fof(f50,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f21])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.28/0.54  fof(f252,plain,(
% 1.28/0.54    spl5_25 | ~spl5_5 | ~spl5_7),
% 1.28/0.54    inference(avatar_split_clause,[],[f246,f85,f77,f250])).
% 1.28/0.54  fof(f246,plain,(
% 1.28/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_5 | ~spl5_7)),
% 1.28/0.54    inference(superposition,[],[f86,f78])).
% 1.28/0.54  fof(f86,plain,(
% 1.28/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_7),
% 1.28/0.54    inference(avatar_component_clause,[],[f85])).
% 1.28/0.54  fof(f242,plain,(
% 1.28/0.54    k1_xboole_0 != sK1 | r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~r1_tarski(k2_relat_1(sK3),sK1)),
% 1.28/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.28/0.54  fof(f241,plain,(
% 1.28/0.54    spl5_23 | spl5_4 | ~spl5_8 | ~spl5_7),
% 1.28/0.54    inference(avatar_split_clause,[],[f234,f85,f89,f74,f237])).
% 1.28/0.54  fof(f234,plain,(
% 1.28/0.54    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl5_7),
% 1.28/0.54    inference(resolution,[],[f52,f86])).
% 1.28/0.54  fof(f52,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f32])).
% 1.28/0.54  fof(f194,plain,(
% 1.28/0.54    ~spl5_10 | ~spl5_1 | ~spl5_13 | spl5_16),
% 1.28/0.54    inference(avatar_split_clause,[],[f172,f150,f141,f64,f107])).
% 1.28/0.54  fof(f141,plain,(
% 1.28/0.54    spl5_13 <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.28/0.54  fof(f150,plain,(
% 1.28/0.54    spl5_16 <=> v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.28/0.54  fof(f172,plain,(
% 1.28/0.54    ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl5_16),
% 1.28/0.54    inference(resolution,[],[f151,f44])).
% 1.28/0.54  fof(f151,plain,(
% 1.28/0.54    ~v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) | spl5_16),
% 1.28/0.54    inference(avatar_component_clause,[],[f150])).
% 1.28/0.54  fof(f152,plain,(
% 1.28/0.54    ~spl5_13 | spl5_14 | spl5_15 | ~spl5_16 | ~spl5_12),
% 1.28/0.54    inference(avatar_split_clause,[],[f139,f134,f150,f147,f144,f141])).
% 1.28/0.54  fof(f147,plain,(
% 1.28/0.54    spl5_15 <=> k1_xboole_0 = k1_relat_1(sK3)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.28/0.54  fof(f139,plain,(
% 1.28/0.54    ~v1_funct_2(sK3,k1_relat_1(sK3),k1_xboole_0) | k1_xboole_0 = k1_relat_1(sK3) | k1_xboole_0 = sK3 | ~r1_tarski(k2_relat_1(sK3),k1_xboole_0) | ~spl5_12),
% 1.28/0.54    inference(resolution,[],[f60,f135])).
% 1.28/0.54  fof(f60,plain,(
% 1.28/0.54    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.28/0.54    inference(equality_resolution,[],[f56])).
% 1.28/0.54  fof(f56,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f32])).
% 1.28/0.54  fof(f136,plain,(
% 1.28/0.54    ~spl5_10 | spl5_12 | ~spl5_1),
% 1.28/0.54    inference(avatar_split_clause,[],[f132,f64,f134,f107])).
% 1.28/0.54  fof(f132,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | ~spl5_1),
% 1.28/0.54    inference(resolution,[],[f45,f92])).
% 1.28/0.54  fof(f92,plain,(
% 1.28/0.54    v1_funct_1(sK3) | ~spl5_1),
% 1.28/0.54    inference(avatar_component_clause,[],[f64])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f18])).
% 1.28/0.54  fof(f115,plain,(
% 1.28/0.54    ~spl5_7 | spl5_10),
% 1.28/0.54    inference(avatar_contradiction_clause,[],[f114])).
% 1.28/0.54  fof(f114,plain,(
% 1.28/0.54    $false | (~spl5_7 | spl5_10)),
% 1.28/0.54    inference(subsumption_resolution,[],[f86,f113])).
% 1.28/0.54  fof(f113,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_10),
% 1.28/0.54    inference(resolution,[],[f108,f49])).
% 1.28/0.54  fof(f49,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.28/0.54  fof(f108,plain,(
% 1.28/0.54    ~v1_relat_1(sK3) | spl5_10),
% 1.28/0.54    inference(avatar_component_clause,[],[f107])).
% 1.28/0.54  fof(f112,plain,(
% 1.28/0.54    ~spl5_10 | spl5_11 | ~spl5_9),
% 1.28/0.54    inference(avatar_split_clause,[],[f105,f102,f110,f107])).
% 1.28/0.54  fof(f102,plain,(
% 1.28/0.54    spl5_9 <=> v5_relat_1(sK3,sK1)),
% 1.28/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.28/0.54  fof(f105,plain,(
% 1.28/0.54    r1_tarski(k2_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | ~spl5_9),
% 1.28/0.54    inference(resolution,[],[f103,f41])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f27])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(nnf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.28/0.54    inference(ennf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.28/0.54  fof(f103,plain,(
% 1.28/0.54    v5_relat_1(sK3,sK1) | ~spl5_9),
% 1.28/0.54    inference(avatar_component_clause,[],[f102])).
% 1.28/0.54  fof(f104,plain,(
% 1.28/0.54    spl5_9 | ~spl5_7),
% 1.28/0.54    inference(avatar_split_clause,[],[f100,f85,f102])).
% 1.28/0.54  fof(f100,plain,(
% 1.28/0.54    v5_relat_1(sK3,sK1) | ~spl5_7),
% 1.28/0.54    inference(resolution,[],[f51,f86])).
% 1.28/0.54  fof(f51,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.28/0.54    inference(ennf_transformation,[],[f12])).
% 1.28/0.54  fof(f12,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.28/0.54    inference(pure_predicate_removal,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.28/0.54  fof(f93,plain,(
% 1.28/0.54    spl5_1),
% 1.28/0.54    inference(avatar_split_clause,[],[f33,f64])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    v1_funct_1(sK3)),
% 1.28/0.54    inference(cnf_transformation,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f25])).
% 1.28/0.54  % (20491)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  % (20492)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.28/0.54  fof(f14,plain,(
% 1.28/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.28/0.54    inference(flattening,[],[f13])).
% 1.28/0.55  % (20489)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.28/0.55  % (20503)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.28/0.55  fof(f13,plain,(
% 1.28/0.55    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.28/0.55    inference(ennf_transformation,[],[f11])).
% 1.28/0.55  fof(f11,negated_conjecture,(
% 1.28/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.28/0.55    inference(negated_conjecture,[],[f10])).
% 1.28/0.55  fof(f10,conjecture,(
% 1.28/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.28/0.55  fof(f91,plain,(
% 1.28/0.55    spl5_8),
% 1.28/0.55    inference(avatar_split_clause,[],[f34,f89])).
% 1.28/0.55  fof(f34,plain,(
% 1.28/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f87,plain,(
% 1.28/0.55    spl5_7),
% 1.28/0.55    inference(avatar_split_clause,[],[f35,f85])).
% 1.28/0.55  fof(f35,plain,(
% 1.28/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f83,plain,(
% 1.28/0.55    spl5_6),
% 1.28/0.55    inference(avatar_split_clause,[],[f36,f81])).
% 1.28/0.55  fof(f36,plain,(
% 1.28/0.55    r1_tarski(sK1,sK2)),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f79,plain,(
% 1.28/0.55    ~spl5_4 | spl5_5),
% 1.28/0.55    inference(avatar_split_clause,[],[f37,f77,f74])).
% 1.28/0.55  fof(f37,plain,(
% 1.28/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f72,plain,(
% 1.28/0.55    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.28/0.55    inference(avatar_split_clause,[],[f38,f70,f67,f64])).
% 1.28/0.55  fof(f38,plain,(
% 1.28/0.55    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  % SZS output end Proof for theBenchmark
% 1.28/0.55  % (20493)------------------------------
% 1.28/0.55  % (20493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (20493)Termination reason: Refutation
% 1.28/0.55  
% 1.28/0.55  % (20493)Memory used [KB]: 11001
% 1.28/0.55  % (20493)Time elapsed: 0.141 s
% 1.28/0.55  % (20493)------------------------------
% 1.28/0.55  % (20493)------------------------------
% 1.28/0.55  % (20491)Refutation not found, incomplete strategy% (20491)------------------------------
% 1.28/0.55  % (20491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (20491)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.55  
% 1.28/0.55  % (20491)Memory used [KB]: 10618
% 1.28/0.55  % (20491)Time elapsed: 0.138 s
% 1.28/0.55  % (20491)------------------------------
% 1.28/0.55  % (20491)------------------------------
% 1.28/0.55  % (20501)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.55  % (20472)Success in time 0.183 s
%------------------------------------------------------------------------------
