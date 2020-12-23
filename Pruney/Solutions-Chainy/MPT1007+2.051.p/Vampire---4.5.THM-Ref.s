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
% DateTime   : Thu Dec  3 13:03:58 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 286 expanded)
%              Number of leaves         :   42 ( 116 expanded)
%              Depth                    :    9
%              Number of atoms          :  470 ( 799 expanded)
%              Number of equality atoms :   95 ( 174 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f694,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f120,f125,f132,f146,f161,f166,f176,f201,f215,f220,f233,f248,f258,f269,f344,f395,f426,f614,f642,f648,f693])).

fof(f693,plain,
    ( ~ spl13_34
    | ~ spl13_41 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | ~ spl13_34
    | ~ spl13_41 ),
    inference(unit_resulting_resolution,[],[f61,f93,f655,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f655,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_34
    | ~ spl13_41 ),
    inference(resolution,[],[f650,f425])).

fof(f425,plain,
    ( sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_34 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl13_34
  <=> sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f650,plain,
    ( ! [X2,X1] :
        ( ~ sP11(k1_xboole_0,X2)
        | ~ r2_hidden(X1,X2) )
    | ~ spl13_41 ),
    inference(resolution,[],[f641,f108])).

fof(f108,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2)
      | ~ r2_hidden(X3,X1)
      | ~ sP11(X2,X1) ) ),
    inference(general_splitting,[],[f85,f107_D])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | sP11(X2,X1) ) ),
    inference(cnf_transformation,[],[f107_D])).

fof(f107_D,plain,(
    ! [X1,X2] :
      ( ! [X0] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | k1_relset_1(X1,X0,X2) != X1 )
    <=> ~ sP11(X2,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) != X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

fof(f641,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_xboole_0)
    | ~ spl13_41 ),
    inference(avatar_component_clause,[],[f640])).

fof(f640,plain,
    ( spl13_41
  <=> ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).

fof(f93,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f52,f90])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f89])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f648,plain,(
    ~ spl13_40 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl13_40 ),
    inference(unit_resulting_resolution,[],[f54,f638,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f638,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f637])).

fof(f637,plain,
    ( spl13_40
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f642,plain,
    ( spl13_40
    | spl13_41
    | ~ spl13_39 ),
    inference(avatar_split_clause,[],[f634,f612,f640,f637])).

fof(f612,plain,
    ( spl13_39
  <=> ! [X5,X4] :
        ( ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).

fof(f634,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_39 ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl13_39 ),
    inference(superposition,[],[f613,f621])).

fof(f621,plain,
    ( ! [X14] :
        ( k1_xboole_0 = k10_relat_1(X14,k1_xboole_0)
        | ~ v1_relat_1(X14) )
    | ~ spl13_39 ),
    inference(resolution,[],[f613,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f613,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))
        | ~ v1_relat_1(X5) )
    | ~ spl13_39 ),
    inference(avatar_component_clause,[],[f612])).

fof(f614,plain,
    ( spl13_39
    | spl13_20
    | ~ spl13_17
    | ~ spl13_22
    | ~ spl13_29 ),
    inference(avatar_split_clause,[],[f608,f392,f266,f231,f255,f612])).

fof(f255,plain,
    ( spl13_20
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f231,plain,
    ( spl13_17
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f266,plain,
    ( spl13_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f392,plain,
    ( spl13_29
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).

fof(f608,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK0,k1_xboole_0)
        | ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) )
    | ~ spl13_17
    | ~ spl13_22
    | ~ spl13_29 ),
    inference(duplicate_literal_removal,[],[f603])).

fof(f603,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK0,k1_xboole_0)
        | ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))
        | ~ v1_relat_1(X5)
        | ~ r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) )
    | ~ spl13_17
    | ~ spl13_22
    | ~ spl13_29 ),
    inference(superposition,[],[f72,f438])).

fof(f438,plain,
    ( ! [X8,X7] :
        ( sK0 = sK5(X7,k1_xboole_0,X8)
        | ~ v1_relat_1(X8)
        | ~ r2_hidden(X7,k10_relat_1(X8,k1_xboole_0)) )
    | ~ spl13_17
    | ~ spl13_22
    | ~ spl13_29 ),
    inference(resolution,[],[f432,f72])).

fof(f432,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | sK0 = X0 )
    | ~ spl13_17
    | ~ spl13_22
    | ~ spl13_29 ),
    inference(forward_demodulation,[],[f363,f394])).

fof(f394,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl13_29 ),
    inference(avatar_component_clause,[],[f392])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | sK0 = X0 )
    | ~ spl13_17
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f232,f268])).

fof(f268,plain,
    ( k1_xboole_0 = sK2
    | ~ spl13_22 ),
    inference(avatar_component_clause,[],[f266])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0 )
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f231])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f426,plain,
    ( spl13_34
    | ~ spl13_14
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f358,f266,f194,f423])).

fof(f194,plain,
    ( spl13_14
  <=> sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f358,plain,
    ( sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_14
    | ~ spl13_22 ),
    inference(backward_demodulation,[],[f196,f268])).

fof(f196,plain,
    ( sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f395,plain,
    ( spl13_29
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(avatar_split_clause,[],[f370,f266,f241,f392])).

fof(f241,plain,
    ( spl13_18
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f370,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl13_18
    | ~ spl13_22 ),
    inference(forward_demodulation,[],[f243,f268])).

fof(f243,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl13_18 ),
    inference(avatar_component_clause,[],[f241])).

fof(f344,plain,
    ( spl13_18
    | spl13_11
    | ~ spl13_19 ),
    inference(avatar_split_clause,[],[f303,f245,f173,f241])).

fof(f173,plain,
    ( spl13_11
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f245,plain,
    ( spl13_19
  <=> sK0 = sK3(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f303,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl13_19 ),
    inference(superposition,[],[f60,f247])).

fof(f247,plain,
    ( sK0 = sK3(k1_relat_1(sK2))
    | ~ spl13_19 ),
    inference(avatar_component_clause,[],[f245])).

fof(f269,plain,
    ( spl13_22
    | ~ spl13_8
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f253,f241,f158,f266])).

fof(f158,plain,
    ( spl13_8
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f253,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl13_18 ),
    inference(trivial_inequality_removal,[],[f252])).

fof(f252,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl13_18 ),
    inference(superposition,[],[f57,f243])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f258,plain,
    ( ~ spl13_20
    | spl13_11
    | ~ spl13_18 ),
    inference(avatar_split_clause,[],[f251,f241,f173,f255])).

fof(f251,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | spl13_11
    | ~ spl13_18 ),
    inference(backward_demodulation,[],[f175,f243])).

fof(f175,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK2))
    | spl13_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f248,plain,
    ( spl13_18
    | spl13_19
    | ~ spl13_17 ),
    inference(avatar_split_clause,[],[f238,f231,f245,f241])).

fof(f238,plain,
    ( sK0 = sK3(k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl13_17 ),
    inference(resolution,[],[f232,f60])).

fof(f233,plain,
    ( ~ spl13_8
    | spl13_17
    | ~ spl13_16 ),
    inference(avatar_split_clause,[],[f228,f218,f231,f158])).

fof(f218,plain,
    ( spl13_16
  <=> ! [X3,X2] :
        ( sK0 = X2
        | ~ r2_hidden(X2,k10_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | sK0 = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl13_16 ),
    inference(superposition,[],[f219,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f219,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k10_relat_1(sK2,X3))
        | sK0 = X2 )
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f218])).

fof(f220,plain,
    ( ~ spl13_8
    | spl13_16
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f206,f143,f218,f158])).

fof(f143,plain,
    ( spl13_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f206,plain,
    ( ! [X2,X3] :
        ( sK0 = X2
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(X2,k10_relat_1(sK2,X3)) )
    | ~ spl13_7 ),
    inference(resolution,[],[f191,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f191,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
        | sK0 = X0 )
    | ~ spl13_7 ),
    inference(superposition,[],[f187,f63])).

fof(f63,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f187,plain,
    ( ! [X0] :
        ( k1_mcart_1(X0) = sK0
        | ~ r2_hidden(X0,sK2) )
    | ~ spl13_7 ),
    inference(resolution,[],[f156,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f86,f90])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
      | k1_mcart_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 )
      | ~ r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f156,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl13_7 ),
    inference(resolution,[],[f145,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f215,plain,
    ( spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | spl13_15 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl13_2
    | ~ spl13_4
    | ~ spl13_7
    | spl13_15 ),
    inference(unit_resulting_resolution,[],[f119,f131,f145,f200,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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

fof(f200,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | spl13_15 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl13_15
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f131,plain,
    ( v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl13_4
  <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f119,plain,
    ( k1_xboole_0 != sK1
    | spl13_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl13_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f201,plain,
    ( spl13_14
    | ~ spl13_15
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f153,f143,f198,f194])).

fof(f153,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)
    | sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl13_7 ),
    inference(resolution,[],[f145,f107])).

fof(f176,plain,
    ( ~ spl13_8
    | ~ spl13_11
    | ~ spl13_1
    | ~ spl13_9
    | spl13_3 ),
    inference(avatar_split_clause,[],[f126,f122,f163,f112,f173,f158])).

fof(f112,plain,
    ( spl13_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f163,plain,
    ( spl13_9
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f122,plain,
    ( spl13_3
  <=> r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f126,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ r2_hidden(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl13_3 ),
    inference(resolution,[],[f124,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f124,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),sK1)
    | spl13_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f166,plain,
    ( spl13_9
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f149,f143,f163])).

fof(f149,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl13_7 ),
    inference(resolution,[],[f145,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f161,plain,
    ( spl13_8
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f147,f143,f158])).

fof(f147,plain,
    ( v1_relat_1(sK2)
    | ~ spl13_7 ),
    inference(resolution,[],[f145,f74])).

fof(f146,plain,(
    spl13_7 ),
    inference(avatar_split_clause,[],[f91,f143])).

fof(f91,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f49,f90])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

fof(f132,plain,(
    spl13_4 ),
    inference(avatar_split_clause,[],[f92,f129])).

fof(f92,plain,(
    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f48,f90])).

fof(f48,plain,(
    v1_funct_2(sK2,k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f125,plain,(
    ~ spl13_3 ),
    inference(avatar_split_clause,[],[f51,f122])).

fof(f51,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f120,plain,(
    ~ spl13_2 ),
    inference(avatar_split_clause,[],[f50,f117])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,(
    spl13_1 ),
    inference(avatar_split_clause,[],[f47,f112])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:09:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (4741)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (4756)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.57  % (4747)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (4744)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (4764)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.57  % (4757)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.58  % (4749)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.59  % (4743)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.59  % (4748)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.59  % (4739)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.59  % (4768)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.59  % (4740)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.60  % (4745)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.60  % (4766)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.60  % (4742)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.60  % (4762)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.60  % (4761)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.60  % (4754)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.61  % (4755)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.61  % (4752)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.61  % (4760)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.62  % (4763)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.62  % (4751)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.62  % (4753)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.62  % (4746)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.91/0.62  % (4767)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.91/0.63  % (4759)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.91/0.63  % (4765)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.91/0.63  % (4758)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.91/0.64  % (4750)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.21/0.66  % (4761)Refutation found. Thanks to Tanya!
% 2.21/0.66  % SZS status Theorem for theBenchmark
% 2.21/0.68  % SZS output start Proof for theBenchmark
% 2.21/0.68  fof(f694,plain,(
% 2.21/0.68    $false),
% 2.21/0.68    inference(avatar_sat_refutation,[],[f115,f120,f125,f132,f146,f161,f166,f176,f201,f215,f220,f233,f248,f258,f269,f344,f395,f426,f614,f642,f648,f693])).
% 2.21/0.68  fof(f693,plain,(
% 2.21/0.68    ~spl13_34 | ~spl13_41),
% 2.21/0.68    inference(avatar_contradiction_clause,[],[f686])).
% 2.21/0.68  fof(f686,plain,(
% 2.21/0.68    $false | (~spl13_34 | ~spl13_41)),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f61,f93,f655,f65])).
% 2.21/0.68  fof(f65,plain,(
% 2.21/0.68    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f33])).
% 2.21/0.68  fof(f33,plain,(
% 2.21/0.68    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.21/0.68    inference(flattening,[],[f32])).
% 2.21/0.68  fof(f32,plain,(
% 2.21/0.68    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.21/0.68    inference(ennf_transformation,[],[f9])).
% 2.21/0.68  fof(f9,axiom,(
% 2.21/0.68    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.21/0.68  fof(f655,plain,(
% 2.21/0.68    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))) ) | (~spl13_34 | ~spl13_41)),
% 2.21/0.68    inference(resolution,[],[f650,f425])).
% 2.21/0.68  fof(f425,plain,(
% 2.21/0.68    sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl13_34),
% 2.21/0.68    inference(avatar_component_clause,[],[f423])).
% 2.21/0.68  fof(f423,plain,(
% 2.21/0.68    spl13_34 <=> sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.21/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).
% 2.21/0.68  fof(f650,plain,(
% 2.21/0.68    ( ! [X2,X1] : (~sP11(k1_xboole_0,X2) | ~r2_hidden(X1,X2)) ) | ~spl13_41),
% 2.21/0.68    inference(resolution,[],[f641,f108])).
% 2.21/0.68  fof(f108,plain,(
% 2.21/0.68    ( ! [X2,X3,X1] : (r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2) | ~r2_hidden(X3,X1) | ~sP11(X2,X1)) )),
% 2.21/0.68    inference(general_splitting,[],[f85,f107_D])).
% 2.21/0.68  fof(f107,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | sP11(X2,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f107_D])).
% 2.21/0.68  fof(f107_D,plain,(
% 2.21/0.68    ( ! [X1,X2] : (( ! [X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1) ) <=> ~sP11(X2,X1)) )),
% 2.21/0.68    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).
% 2.21/0.68  fof(f85,plain,(
% 2.21/0.68    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) != X1 | ~r2_hidden(X3,X1) | r2_hidden(k4_tarski(X3,sK7(X2,X3)),X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f43])).
% 2.21/0.68  fof(f43,plain,(
% 2.21/0.68    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.21/0.68    inference(ennf_transformation,[],[f18])).
% 2.21/0.68  fof(f18,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).
% 2.21/0.68  fof(f641,plain,(
% 2.21/0.68    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) ) | ~spl13_41),
% 2.21/0.68    inference(avatar_component_clause,[],[f640])).
% 2.21/0.68  fof(f640,plain,(
% 2.21/0.68    spl13_41 <=> ! [X1] : ~r2_hidden(X1,k1_xboole_0)),
% 2.21/0.68    introduced(avatar_definition,[new_symbols(naming,[spl13_41])])).
% 2.21/0.68  fof(f93,plain,(
% 2.21/0.68    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 2.21/0.68    inference(definition_unfolding,[],[f52,f90])).
% 2.21/0.68  fof(f90,plain,(
% 2.21/0.68    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.21/0.68    inference(definition_unfolding,[],[f55,f89])).
% 2.21/0.68  fof(f89,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.21/0.68    inference(definition_unfolding,[],[f62,f69])).
% 2.21/0.68  fof(f69,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f4])).
% 2.21/0.68  fof(f4,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.21/0.68  fof(f62,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f3])).
% 2.21/0.68  fof(f3,axiom,(
% 2.21/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.21/0.68  fof(f55,plain,(
% 2.21/0.68    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f2])).
% 2.21/0.68  fof(f2,axiom,(
% 2.21/0.68    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.21/0.68  fof(f52,plain,(
% 2.21/0.68    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f5])).
% 2.21/0.68  fof(f5,axiom,(
% 2.21/0.68    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 2.21/0.68  fof(f61,plain,(
% 2.21/0.68    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f6])).
% 2.21/0.68  fof(f6,axiom,(
% 2.21/0.68    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 2.21/0.68  fof(f648,plain,(
% 2.21/0.68    ~spl13_40),
% 2.21/0.68    inference(avatar_contradiction_clause,[],[f644])).
% 2.21/0.68  fof(f644,plain,(
% 2.21/0.68    $false | ~spl13_40),
% 2.21/0.68    inference(unit_resulting_resolution,[],[f54,f638,f74])).
% 2.21/0.68  fof(f74,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f39])).
% 2.21/0.68  fof(f39,plain,(
% 2.21/0.68    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.68    inference(ennf_transformation,[],[f16])).
% 2.21/0.68  fof(f16,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.21/0.69  fof(f638,plain,(
% 2.21/0.69    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl13_40),
% 2.21/0.69    inference(avatar_component_clause,[],[f637])).
% 2.21/0.69  fof(f637,plain,(
% 2.21/0.69    spl13_40 <=> ! [X0] : ~v1_relat_1(X0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).
% 2.21/0.69  fof(f54,plain,(
% 2.21/0.69    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.21/0.69    inference(cnf_transformation,[],[f8])).
% 2.21/0.69  fof(f8,axiom,(
% 2.21/0.69    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.21/0.69  fof(f642,plain,(
% 2.21/0.69    spl13_40 | spl13_41 | ~spl13_39),
% 2.21/0.69    inference(avatar_split_clause,[],[f634,f612,f640,f637])).
% 2.21/0.69  fof(f612,plain,(
% 2.21/0.69    spl13_39 <=> ! [X5,X4] : (~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_39])])).
% 2.21/0.69  fof(f634,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl13_39),
% 2.21/0.69    inference(duplicate_literal_removal,[],[f624])).
% 2.21/0.69  fof(f624,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) ) | ~spl13_39),
% 2.21/0.69    inference(superposition,[],[f613,f621])).
% 2.21/0.69  fof(f621,plain,(
% 2.21/0.69    ( ! [X14] : (k1_xboole_0 = k10_relat_1(X14,k1_xboole_0) | ~v1_relat_1(X14)) ) | ~spl13_39),
% 2.21/0.69    inference(resolution,[],[f613,f60])).
% 2.21/0.69  fof(f60,plain,(
% 2.21/0.69    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.21/0.69    inference(cnf_transformation,[],[f31])).
% 2.21/0.69  fof(f31,plain,(
% 2.21/0.69    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.21/0.69    inference(flattening,[],[f30])).
% 2.21/0.69  fof(f30,plain,(
% 2.21/0.69    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.21/0.69    inference(ennf_transformation,[],[f20])).
% 2.21/0.69  fof(f20,axiom,(
% 2.21/0.69    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 2.21/0.69  fof(f613,plain,(
% 2.21/0.69    ( ! [X4,X5] : (~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) | ~v1_relat_1(X5)) ) | ~spl13_39),
% 2.21/0.69    inference(avatar_component_clause,[],[f612])).
% 2.21/0.69  fof(f614,plain,(
% 2.21/0.69    spl13_39 | spl13_20 | ~spl13_17 | ~spl13_22 | ~spl13_29),
% 2.21/0.69    inference(avatar_split_clause,[],[f608,f392,f266,f231,f255,f612])).
% 2.21/0.69  fof(f255,plain,(
% 2.21/0.69    spl13_20 <=> r2_hidden(sK0,k1_xboole_0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).
% 2.21/0.69  fof(f231,plain,(
% 2.21/0.69    spl13_17 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).
% 2.21/0.69  fof(f266,plain,(
% 2.21/0.69    spl13_22 <=> k1_xboole_0 = sK2),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).
% 2.21/0.69  fof(f392,plain,(
% 2.21/0.69    spl13_29 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_29])])).
% 2.21/0.69  fof(f608,plain,(
% 2.21/0.69    ( ! [X4,X5] : (r2_hidden(sK0,k1_xboole_0) | ~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))) ) | (~spl13_17 | ~spl13_22 | ~spl13_29)),
% 2.21/0.69    inference(duplicate_literal_removal,[],[f603])).
% 2.21/0.69  fof(f603,plain,(
% 2.21/0.69    ( ! [X4,X5] : (r2_hidden(sK0,k1_xboole_0) | ~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0)) | ~v1_relat_1(X5) | ~r2_hidden(X4,k10_relat_1(X5,k1_xboole_0))) ) | (~spl13_17 | ~spl13_22 | ~spl13_29)),
% 2.21/0.69    inference(superposition,[],[f72,f438])).
% 2.21/0.69  fof(f438,plain,(
% 2.21/0.69    ( ! [X8,X7] : (sK0 = sK5(X7,k1_xboole_0,X8) | ~v1_relat_1(X8) | ~r2_hidden(X7,k10_relat_1(X8,k1_xboole_0))) ) | (~spl13_17 | ~spl13_22 | ~spl13_29)),
% 2.21/0.69    inference(resolution,[],[f432,f72])).
% 2.21/0.69  fof(f432,plain,(
% 2.21/0.69    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | sK0 = X0) ) | (~spl13_17 | ~spl13_22 | ~spl13_29)),
% 2.21/0.69    inference(forward_demodulation,[],[f363,f394])).
% 2.21/0.69  fof(f394,plain,(
% 2.21/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl13_29),
% 2.21/0.69    inference(avatar_component_clause,[],[f392])).
% 2.21/0.69  fof(f363,plain,(
% 2.21/0.69    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | sK0 = X0) ) | (~spl13_17 | ~spl13_22)),
% 2.21/0.69    inference(backward_demodulation,[],[f232,f268])).
% 2.21/0.69  fof(f268,plain,(
% 2.21/0.69    k1_xboole_0 = sK2 | ~spl13_22),
% 2.21/0.69    inference(avatar_component_clause,[],[f266])).
% 2.21/0.69  fof(f232,plain,(
% 2.21/0.69    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0) ) | ~spl13_17),
% 2.21/0.69    inference(avatar_component_clause,[],[f231])).
% 2.21/0.69  fof(f72,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 2.21/0.69    inference(cnf_transformation,[],[f38])).
% 2.21/0.69  fof(f38,plain,(
% 2.21/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.21/0.69    inference(ennf_transformation,[],[f11])).
% 2.21/0.69  fof(f11,axiom,(
% 2.21/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 2.21/0.69  fof(f426,plain,(
% 2.21/0.69    spl13_34 | ~spl13_14 | ~spl13_22),
% 2.21/0.69    inference(avatar_split_clause,[],[f358,f266,f194,f423])).
% 2.21/0.69  fof(f194,plain,(
% 2.21/0.69    spl13_14 <=> sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).
% 2.21/0.69  fof(f358,plain,(
% 2.21/0.69    sP11(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl13_14 | ~spl13_22)),
% 2.21/0.69    inference(backward_demodulation,[],[f196,f268])).
% 2.21/0.69  fof(f196,plain,(
% 2.21/0.69    sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl13_14),
% 2.21/0.69    inference(avatar_component_clause,[],[f194])).
% 2.21/0.69  fof(f395,plain,(
% 2.21/0.69    spl13_29 | ~spl13_18 | ~spl13_22),
% 2.21/0.69    inference(avatar_split_clause,[],[f370,f266,f241,f392])).
% 2.21/0.69  fof(f241,plain,(
% 2.21/0.69    spl13_18 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).
% 2.21/0.69  fof(f370,plain,(
% 2.21/0.69    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl13_18 | ~spl13_22)),
% 2.21/0.69    inference(forward_demodulation,[],[f243,f268])).
% 2.21/0.69  fof(f243,plain,(
% 2.21/0.69    k1_xboole_0 = k1_relat_1(sK2) | ~spl13_18),
% 2.21/0.69    inference(avatar_component_clause,[],[f241])).
% 2.21/0.69  fof(f344,plain,(
% 2.21/0.69    spl13_18 | spl13_11 | ~spl13_19),
% 2.21/0.69    inference(avatar_split_clause,[],[f303,f245,f173,f241])).
% 2.21/0.69  fof(f173,plain,(
% 2.21/0.69    spl13_11 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).
% 2.21/0.69  fof(f245,plain,(
% 2.21/0.69    spl13_19 <=> sK0 = sK3(k1_relat_1(sK2))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).
% 2.21/0.69  fof(f303,plain,(
% 2.21/0.69    r2_hidden(sK0,k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl13_19),
% 2.21/0.69    inference(superposition,[],[f60,f247])).
% 2.21/0.69  fof(f247,plain,(
% 2.21/0.69    sK0 = sK3(k1_relat_1(sK2)) | ~spl13_19),
% 2.21/0.69    inference(avatar_component_clause,[],[f245])).
% 2.21/0.69  fof(f269,plain,(
% 2.21/0.69    spl13_22 | ~spl13_8 | ~spl13_18),
% 2.21/0.69    inference(avatar_split_clause,[],[f253,f241,f158,f266])).
% 2.21/0.69  fof(f158,plain,(
% 2.21/0.69    spl13_8 <=> v1_relat_1(sK2)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).
% 2.21/0.69  fof(f253,plain,(
% 2.21/0.69    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl13_18),
% 2.21/0.69    inference(trivial_inequality_removal,[],[f252])).
% 2.21/0.69  fof(f252,plain,(
% 2.21/0.69    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl13_18),
% 2.21/0.69    inference(superposition,[],[f57,f243])).
% 2.21/0.69  fof(f57,plain,(
% 2.21/0.69    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 2.21/0.69    inference(cnf_transformation,[],[f29])).
% 2.21/0.69  fof(f29,plain,(
% 2.21/0.69    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.21/0.69    inference(flattening,[],[f28])).
% 2.21/0.69  fof(f28,plain,(
% 2.21/0.69    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f13])).
% 2.21/0.69  fof(f13,axiom,(
% 2.21/0.69    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.21/0.69  fof(f258,plain,(
% 2.21/0.69    ~spl13_20 | spl13_11 | ~spl13_18),
% 2.21/0.69    inference(avatar_split_clause,[],[f251,f241,f173,f255])).
% 2.21/0.69  fof(f251,plain,(
% 2.21/0.69    ~r2_hidden(sK0,k1_xboole_0) | (spl13_11 | ~spl13_18)),
% 2.21/0.69    inference(backward_demodulation,[],[f175,f243])).
% 2.21/0.69  fof(f175,plain,(
% 2.21/0.69    ~r2_hidden(sK0,k1_relat_1(sK2)) | spl13_11),
% 2.21/0.69    inference(avatar_component_clause,[],[f173])).
% 2.21/0.69  fof(f248,plain,(
% 2.21/0.69    spl13_18 | spl13_19 | ~spl13_17),
% 2.21/0.69    inference(avatar_split_clause,[],[f238,f231,f245,f241])).
% 2.21/0.69  fof(f238,plain,(
% 2.21/0.69    sK0 = sK3(k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | ~spl13_17),
% 2.21/0.69    inference(resolution,[],[f232,f60])).
% 2.21/0.69  fof(f233,plain,(
% 2.21/0.69    ~spl13_8 | spl13_17 | ~spl13_16),
% 2.21/0.69    inference(avatar_split_clause,[],[f228,f218,f231,f158])).
% 2.21/0.69  fof(f218,plain,(
% 2.21/0.69    spl13_16 <=> ! [X3,X2] : (sK0 = X2 | ~r2_hidden(X2,k10_relat_1(sK2,X3)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).
% 2.21/0.69  fof(f228,plain,(
% 2.21/0.69    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | sK0 = X0 | ~v1_relat_1(sK2)) ) | ~spl13_16),
% 2.21/0.69    inference(superposition,[],[f219,f56])).
% 2.21/0.69  fof(f56,plain,(
% 2.21/0.69    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f27])).
% 2.21/0.69  fof(f27,plain,(
% 2.21/0.69    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.69    inference(ennf_transformation,[],[f12])).
% 2.21/0.69  fof(f12,axiom,(
% 2.21/0.69    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 2.21/0.69  fof(f219,plain,(
% 2.21/0.69    ( ! [X2,X3] : (~r2_hidden(X2,k10_relat_1(sK2,X3)) | sK0 = X2) ) | ~spl13_16),
% 2.21/0.69    inference(avatar_component_clause,[],[f218])).
% 2.21/0.69  fof(f220,plain,(
% 2.21/0.69    ~spl13_8 | spl13_16 | ~spl13_7),
% 2.21/0.69    inference(avatar_split_clause,[],[f206,f143,f218,f158])).
% 2.21/0.69  fof(f143,plain,(
% 2.21/0.69    spl13_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).
% 2.21/0.69  fof(f206,plain,(
% 2.21/0.69    ( ! [X2,X3] : (sK0 = X2 | ~v1_relat_1(sK2) | ~r2_hidden(X2,k10_relat_1(sK2,X3))) ) | ~spl13_7),
% 2.21/0.69    inference(resolution,[],[f191,f71])).
% 2.21/0.69  fof(f71,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK5(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 2.21/0.69    inference(cnf_transformation,[],[f38])).
% 2.21/0.69  fof(f191,plain,(
% 2.21/0.69    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | sK0 = X0) ) | ~spl13_7),
% 2.21/0.69    inference(superposition,[],[f187,f63])).
% 2.21/0.69  fof(f63,plain,(
% 2.21/0.69    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 2.21/0.69    inference(cnf_transformation,[],[f21])).
% 2.21/0.69  fof(f21,axiom,(
% 2.21/0.69    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 2.21/0.69  fof(f187,plain,(
% 2.21/0.69    ( ! [X0] : (k1_mcart_1(X0) = sK0 | ~r2_hidden(X0,sK2)) ) | ~spl13_7),
% 2.21/0.69    inference(resolution,[],[f156,f95])).
% 2.21/0.69  fof(f95,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)) | k1_mcart_1(X0) = X1) )),
% 2.21/0.69    inference(definition_unfolding,[],[f86,f90])).
% 2.21/0.69  fof(f86,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) | k1_mcart_1(X0) = X1) )),
% 2.21/0.69    inference(cnf_transformation,[],[f44])).
% 2.21/0.69  fof(f44,plain,(
% 2.21/0.69    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1) | ~r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 2.21/0.69    inference(ennf_transformation,[],[f19])).
% 2.21/0.69  fof(f19,axiom,(
% 2.21/0.69    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 2.21/0.69  fof(f156,plain,(
% 2.21/0.69    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl13_7),
% 2.21/0.69    inference(resolution,[],[f145,f66])).
% 2.21/0.69  fof(f66,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f34])).
% 2.21/0.69  fof(f34,plain,(
% 2.21/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.69    inference(ennf_transformation,[],[f7])).
% 2.21/0.69  fof(f7,axiom,(
% 2.21/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 2.21/0.69  fof(f145,plain,(
% 2.21/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) | ~spl13_7),
% 2.21/0.69    inference(avatar_component_clause,[],[f143])).
% 2.21/0.69  fof(f215,plain,(
% 2.21/0.69    spl13_2 | ~spl13_4 | ~spl13_7 | spl13_15),
% 2.21/0.69    inference(avatar_contradiction_clause,[],[f214])).
% 2.21/0.69  fof(f214,plain,(
% 2.21/0.69    $false | (spl13_2 | ~spl13_4 | ~spl13_7 | spl13_15)),
% 2.21/0.69    inference(unit_resulting_resolution,[],[f119,f131,f145,f200,f82])).
% 2.21/0.69  fof(f82,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f42])).
% 2.21/0.69  fof(f42,plain,(
% 2.21/0.69    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.69    inference(flattening,[],[f41])).
% 2.21/0.69  fof(f41,plain,(
% 2.21/0.69    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.69    inference(ennf_transformation,[],[f22])).
% 2.21/0.69  fof(f22,axiom,(
% 2.21/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.21/0.69  fof(f200,plain,(
% 2.21/0.69    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | spl13_15),
% 2.21/0.69    inference(avatar_component_clause,[],[f198])).
% 2.21/0.69  fof(f198,plain,(
% 2.21/0.69    spl13_15 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).
% 2.21/0.69  fof(f131,plain,(
% 2.21/0.69    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl13_4),
% 2.21/0.69    inference(avatar_component_clause,[],[f129])).
% 2.21/0.69  fof(f129,plain,(
% 2.21/0.69    spl13_4 <=> v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).
% 2.21/0.69  fof(f119,plain,(
% 2.21/0.69    k1_xboole_0 != sK1 | spl13_2),
% 2.21/0.69    inference(avatar_component_clause,[],[f117])).
% 2.21/0.69  fof(f117,plain,(
% 2.21/0.69    spl13_2 <=> k1_xboole_0 = sK1),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).
% 2.21/0.69  fof(f201,plain,(
% 2.21/0.69    spl13_14 | ~spl13_15 | ~spl13_7),
% 2.21/0.69    inference(avatar_split_clause,[],[f153,f143,f198,f194])).
% 2.21/0.69  fof(f153,plain,(
% 2.21/0.69    k2_enumset1(sK0,sK0,sK0,sK0) != k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK2) | sP11(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl13_7),
% 2.21/0.69    inference(resolution,[],[f145,f107])).
% 2.21/0.69  fof(f176,plain,(
% 2.21/0.69    ~spl13_8 | ~spl13_11 | ~spl13_1 | ~spl13_9 | spl13_3),
% 2.21/0.69    inference(avatar_split_clause,[],[f126,f122,f163,f112,f173,f158])).
% 2.21/0.69  fof(f112,plain,(
% 2.21/0.69    spl13_1 <=> v1_funct_1(sK2)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).
% 2.21/0.69  fof(f163,plain,(
% 2.21/0.69    spl13_9 <=> v5_relat_1(sK2,sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).
% 2.21/0.69  fof(f122,plain,(
% 2.21/0.69    spl13_3 <=> r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 2.21/0.69    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).
% 2.21/0.69  fof(f126,plain,(
% 2.21/0.69    ~v5_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl13_3),
% 2.21/0.69    inference(resolution,[],[f124,f67])).
% 2.21/0.69  fof(f67,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f36])).
% 2.21/0.69  fof(f36,plain,(
% 2.21/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.21/0.69    inference(flattening,[],[f35])).
% 2.21/0.69  fof(f35,plain,(
% 2.21/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.21/0.69    inference(ennf_transformation,[],[f14])).
% 2.21/0.69  fof(f14,axiom,(
% 2.21/0.69    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 2.21/0.69  fof(f124,plain,(
% 2.21/0.69    ~r2_hidden(k1_funct_1(sK2,sK0),sK1) | spl13_3),
% 2.21/0.69    inference(avatar_component_clause,[],[f122])).
% 2.21/0.69  fof(f166,plain,(
% 2.21/0.69    spl13_9 | ~spl13_7),
% 2.21/0.69    inference(avatar_split_clause,[],[f149,f143,f163])).
% 2.21/0.69  fof(f149,plain,(
% 2.21/0.69    v5_relat_1(sK2,sK1) | ~spl13_7),
% 2.21/0.69    inference(resolution,[],[f145,f76])).
% 2.21/0.69  fof(f76,plain,(
% 2.21/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 2.21/0.69    inference(cnf_transformation,[],[f40])).
% 2.21/0.69  fof(f40,plain,(
% 2.21/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.69    inference(ennf_transformation,[],[f17])).
% 2.21/0.69  fof(f17,axiom,(
% 2.21/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.21/0.69  fof(f161,plain,(
% 2.21/0.69    spl13_8 | ~spl13_7),
% 2.21/0.69    inference(avatar_split_clause,[],[f147,f143,f158])).
% 2.21/0.69  fof(f147,plain,(
% 2.21/0.69    v1_relat_1(sK2) | ~spl13_7),
% 2.21/0.69    inference(resolution,[],[f145,f74])).
% 2.21/0.69  fof(f146,plain,(
% 2.21/0.69    spl13_7),
% 2.21/0.69    inference(avatar_split_clause,[],[f91,f143])).
% 2.21/0.69  fof(f91,plain,(
% 2.21/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.21/0.69    inference(definition_unfolding,[],[f49,f90])).
% 2.21/0.69  fof(f49,plain,(
% 2.21/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.21/0.69    inference(cnf_transformation,[],[f26])).
% 2.21/0.69  fof(f26,plain,(
% 2.21/0.69    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 2.21/0.69    inference(flattening,[],[f25])).
% 2.21/0.69  fof(f25,plain,(
% 2.21/0.69    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 2.21/0.69    inference(ennf_transformation,[],[f24])).
% 2.21/0.69  fof(f24,negated_conjecture,(
% 2.21/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.21/0.69    inference(negated_conjecture,[],[f23])).
% 2.21/0.69  fof(f23,conjecture,(
% 2.21/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 2.21/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).
% 2.21/0.69  fof(f132,plain,(
% 2.21/0.69    spl13_4),
% 2.21/0.69    inference(avatar_split_clause,[],[f92,f129])).
% 2.21/0.69  fof(f92,plain,(
% 2.21/0.69    v1_funct_2(sK2,k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 2.21/0.69    inference(definition_unfolding,[],[f48,f90])).
% 2.21/0.69  fof(f48,plain,(
% 2.21/0.69    v1_funct_2(sK2,k1_tarski(sK0),sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f26])).
% 2.21/0.69  fof(f125,plain,(
% 2.21/0.69    ~spl13_3),
% 2.21/0.69    inference(avatar_split_clause,[],[f51,f122])).
% 2.21/0.69  fof(f51,plain,(
% 2.21/0.69    ~r2_hidden(k1_funct_1(sK2,sK0),sK1)),
% 2.21/0.69    inference(cnf_transformation,[],[f26])).
% 2.21/0.69  fof(f120,plain,(
% 2.21/0.69    ~spl13_2),
% 2.21/0.69    inference(avatar_split_clause,[],[f50,f117])).
% 2.21/0.69  fof(f50,plain,(
% 2.21/0.69    k1_xboole_0 != sK1),
% 2.21/0.69    inference(cnf_transformation,[],[f26])).
% 2.21/0.69  fof(f115,plain,(
% 2.21/0.69    spl13_1),
% 2.21/0.69    inference(avatar_split_clause,[],[f47,f112])).
% 2.21/0.69  fof(f47,plain,(
% 2.21/0.69    v1_funct_1(sK2)),
% 2.21/0.69    inference(cnf_transformation,[],[f26])).
% 2.21/0.69  % SZS output end Proof for theBenchmark
% 2.21/0.69  % (4761)------------------------------
% 2.21/0.69  % (4761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.69  % (4761)Termination reason: Refutation
% 2.21/0.69  
% 2.21/0.69  % (4761)Memory used [KB]: 11001
% 2.21/0.69  % (4761)Time elapsed: 0.239 s
% 2.21/0.69  % (4761)------------------------------
% 2.21/0.69  % (4761)------------------------------
% 2.21/0.69  % (4738)Success in time 0.328 s
%------------------------------------------------------------------------------
