%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:31 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 237 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  367 ( 858 expanded)
%              Number of equality atoms :   38 (  68 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f451,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f86,f90,f94,f306,f337,f356,f381,f389,f395,f398,f399,f404,f422,f423,f447,f450])).

fof(f450,plain,
    ( spl8_13
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f449,f445,f354])).

fof(f354,plain,
    ( spl8_13
  <=> r2_hidden(sK1,k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f445,plain,
    ( spl8_19
  <=> r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f449,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_19 ),
    inference(resolution,[],[f446,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f446,plain,
    ( r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f445])).

fof(f447,plain,
    ( spl8_8
    | spl8_19
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f443,f387,f445,f152])).

fof(f152,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f387,plain,
    ( spl8_18
  <=> ! [X0] :
        ( r2_hidden(sK1,sK6(sK2,X0))
        | r1_tarski(X0,k1_setfam_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f443,plain,
    ( r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl8_18 ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,
    ( r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))
    | r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))
    | k1_xboole_0 = sK2
    | ~ spl8_18 ),
    inference(resolution,[],[f388,f187])).

fof(f187,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,sK6(X2,k1_tarski(X3)))
      | r1_tarski(k1_tarski(X3),k1_setfam_1(X2))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f62,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK6(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ( ~ r1_tarski(X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(X1,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f388,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK6(sK2,X0))
        | r1_tarski(X0,k1_setfam_1(sK2)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f387])).

fof(f423,plain,
    ( spl8_8
    | spl8_18
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f417,f354,f387,f152])).

fof(f417,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK6(sK2,X0))
        | k1_xboole_0 = sK2
        | r1_tarski(X0,k1_setfam_1(sK2)) )
    | ~ spl8_13 ),
    inference(resolution,[],[f413,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(sK1,X0) )
    | ~ spl8_13 ),
    inference(resolution,[],[f406,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f406,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_setfam_1(sK2),X0)
        | r2_hidden(sK1,X0) )
    | ~ spl8_13 ),
    inference(resolution,[],[f355,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f355,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f354])).

fof(f422,plain,
    ( spl8_2
    | ~ spl8_3
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f416,f354,f79,f75])).

fof(f75,plain,
    ( spl8_2
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f79,plain,
    ( spl8_3
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f416,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl8_3
    | ~ spl8_13 ),
    inference(resolution,[],[f413,f80])).

fof(f80,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f404,plain,(
    ~ spl8_11 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl8_11 ),
    inference(resolution,[],[f336,f120])).

fof(f120,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f118,f51])).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(X1)))
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f97,f54])).

fof(f54,plain,(
    ! [X0] : v1_xboole_0(sK4(X0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_xboole_0(sK4(X0))
      & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0) ) ),
    inference(resolution,[],[f52,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f336,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl8_11
  <=> r2_hidden(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f399,plain,
    ( k1_xboole_0 != sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f398,plain,
    ( ~ spl8_16
    | ~ spl8_5
    | spl8_12 ),
    inference(avatar_split_clause,[],[f396,f339,f88,f372])).

fof(f372,plain,
    ( spl8_16
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f88,plain,
    ( spl8_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f339,plain,
    ( spl8_12
  <=> r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f396,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl8_12 ),
    inference(superposition,[],[f394,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f394,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl8_12 ),
    inference(avatar_component_clause,[],[f339])).

fof(f395,plain,
    ( ~ spl8_12
    | spl8_1
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f393,f152,f72,f339])).

fof(f72,plain,
    ( spl8_1
  <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f393,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))
    | spl8_1
    | ~ spl8_8 ),
    inference(superposition,[],[f73,f153])).

fof(f153,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f73,plain,
    ( ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f389,plain,
    ( spl8_8
    | spl8_18
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f382,f84,f387,f152])).

fof(f84,plain,
    ( spl8_4
  <=> ! [X4] :
        ( r2_hidden(sK1,X4)
        | ~ r2_hidden(X4,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f382,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,sK6(sK2,X0))
        | k1_xboole_0 = sK2
        | r1_tarski(X0,k1_setfam_1(sK2)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK2)
        | r2_hidden(sK1,X4) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f381,plain,
    ( ~ spl8_13
    | spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f361,f304,f72,f354])).

fof(f304,plain,
    ( spl8_10
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f361,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(sK2))
    | spl8_1
    | ~ spl8_10 ),
    inference(forward_demodulation,[],[f73,f305])).

fof(f305,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f304])).

fof(f356,plain,
    ( spl8_13
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f342,f304,f72,f354])).

fof(f342,plain,
    ( r2_hidden(sK1,k1_setfam_1(sK2))
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(superposition,[],[f82,f305])).

fof(f82,plain,
    ( r2_hidden(sK1,k8_setfam_1(sK0,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f337,plain,
    ( spl8_11
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f307,f152,f79,f335])).

fof(f307,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_8 ),
    inference(superposition,[],[f80,f153])).

fof(f306,plain,
    ( spl8_10
    | spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f298,f92,f152,f304])).

fof(f92,plain,
    ( spl8_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f298,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f227,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f227,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f59,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f94,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

% (21420)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f34,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_hidden(sK3,sK2) )
      | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & ( ! [X4] :
          ( r2_hidden(sK1,X4)
          | ~ r2_hidden(X4,sK2) )
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
    & r2_hidden(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_hidden(X3,X2) )
          | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & ( ! [X4] :
              ( r2_hidden(X1,X4)
              | ~ r2_hidden(X4,X2) )
          | r2_hidden(X1,k8_setfam_1(X0,X2)) )
        & r2_hidden(X1,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ? [X3] :
            ( ~ r2_hidden(sK1,X3)
            & r2_hidden(X3,sK2) )
        | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & ( ! [X4] :
            ( r2_hidden(sK1,X4)
            | ~ r2_hidden(X4,sK2) )
        | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) )
      & r2_hidden(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,X3)
        & r2_hidden(X3,sK2) )
   => ( ~ r2_hidden(sK1,sK3)
      & r2_hidden(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X4] :
            ( r2_hidden(X1,X4)
            | ~ r2_hidden(X4,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_hidden(X3,X2) )
        | ~ r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & ( ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) )
        | r2_hidden(X1,k8_setfam_1(X0,X2)) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,k8_setfam_1(X0,X2))
      <~> ! [X3] :
            ( r2_hidden(X1,X3)
            | ~ r2_hidden(X3,X2) ) )
      & r2_hidden(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( r2_hidden(X1,X0)
         => ( r2_hidden(X1,k8_setfam_1(X0,X2))
          <=> ! [X3] :
                ( r2_hidden(X3,X2)
               => r2_hidden(X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( r2_hidden(X1,X0)
       => ( r2_hidden(X1,k8_setfam_1(X0,X2))
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).

fof(f90,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,
    ( spl8_1
    | spl8_4 ),
    inference(avatar_split_clause,[],[f48,f84,f72])).

fof(f48,plain,(
    ! [X4] :
      ( r2_hidden(sK1,X4)
      | ~ r2_hidden(X4,sK2)
      | r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f49,f79,f72])).

fof(f49,plain,
    ( r2_hidden(sK3,sK2)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f50,f75,f72])).

fof(f50,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,k8_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (21404)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.49  % (21403)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (21419)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.50  % (21412)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (21427)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (21422)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (21413)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (21409)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (21429)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (21411)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21409)Refutation not found, incomplete strategy% (21409)------------------------------
% 0.21/0.51  % (21409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21409)Memory used [KB]: 10618
% 0.21/0.51  % (21409)Time elapsed: 0.059 s
% 0.21/0.51  % (21409)------------------------------
% 0.21/0.51  % (21409)------------------------------
% 0.21/0.51  % (21408)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (21414)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (21400)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21399)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (21401)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21402)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (21405)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (21423)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21428)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.54  % (21407)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.54  % (21415)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.54  % (21425)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.54  % (21419)Refutation found. Thanks to Tanya!
% 1.42/0.54  % SZS status Theorem for theBenchmark
% 1.42/0.54  % SZS output start Proof for theBenchmark
% 1.42/0.54  fof(f451,plain,(
% 1.42/0.54    $false),
% 1.42/0.54    inference(avatar_sat_refutation,[],[f77,f81,f86,f90,f94,f306,f337,f356,f381,f389,f395,f398,f399,f404,f422,f423,f447,f450])).
% 1.42/0.54  fof(f450,plain,(
% 1.42/0.54    spl8_13 | ~spl8_19),
% 1.42/0.54    inference(avatar_split_clause,[],[f449,f445,f354])).
% 1.42/0.54  fof(f354,plain,(
% 1.42/0.54    spl8_13 <=> r2_hidden(sK1,k1_setfam_1(sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.42/0.54  fof(f445,plain,(
% 1.42/0.54    spl8_19 <=> r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.42/0.54  fof(f449,plain,(
% 1.42/0.54    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl8_19),
% 1.42/0.54    inference(resolution,[],[f446,f66])).
% 1.42/0.54  fof(f66,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f45,plain,(
% 1.42/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.42/0.54    inference(nnf_transformation,[],[f3])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.42/0.54  fof(f446,plain,(
% 1.42/0.54    r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) | ~spl8_19),
% 1.42/0.54    inference(avatar_component_clause,[],[f445])).
% 1.42/0.54  fof(f447,plain,(
% 1.42/0.54    spl8_8 | spl8_19 | ~spl8_18),
% 1.42/0.54    inference(avatar_split_clause,[],[f443,f387,f445,f152])).
% 1.42/0.54  fof(f152,plain,(
% 1.42/0.54    spl8_8 <=> k1_xboole_0 = sK2),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.42/0.54  fof(f387,plain,(
% 1.42/0.54    spl8_18 <=> ! [X0] : (r2_hidden(sK1,sK6(sK2,X0)) | r1_tarski(X0,k1_setfam_1(sK2)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.42/0.54  fof(f443,plain,(
% 1.42/0.54    r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl8_18),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f441])).
% 1.42/0.54  fof(f441,plain,(
% 1.42/0.54    r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) | r1_tarski(k1_tarski(sK1),k1_setfam_1(sK2)) | k1_xboole_0 = sK2 | ~spl8_18),
% 1.42/0.54    inference(resolution,[],[f388,f187])).
% 1.42/0.54  fof(f187,plain,(
% 1.42/0.54    ( ! [X2,X3] : (~r2_hidden(X3,sK6(X2,k1_tarski(X3))) | r1_tarski(k1_tarski(X3),k1_setfam_1(X2)) | k1_xboole_0 = X2) )),
% 1.42/0.54    inference(resolution,[],[f62,f67])).
% 1.42/0.54  fof(f67,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f45])).
% 1.42/0.54  fof(f62,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK6(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f40])).
% 1.42/0.54  fof(f40,plain,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | (~r1_tarski(X1,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f24,f39])).
% 1.42/0.54  fof(f39,plain,(
% 1.42/0.54    ! [X1,X0] : (? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)) => (~r1_tarski(X1,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),X0)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.42/0.54    inference(flattening,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f12])).
% 1.42/0.54  fof(f12,axiom,(
% 1.42/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.42/0.54  fof(f388,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK1,sK6(sK2,X0)) | r1_tarski(X0,k1_setfam_1(sK2))) ) | ~spl8_18),
% 1.42/0.54    inference(avatar_component_clause,[],[f387])).
% 1.42/0.54  fof(f423,plain,(
% 1.42/0.54    spl8_8 | spl8_18 | ~spl8_13),
% 1.42/0.54    inference(avatar_split_clause,[],[f417,f354,f387,f152])).
% 1.42/0.54  fof(f417,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK1,sK6(sK2,X0)) | k1_xboole_0 = sK2 | r1_tarski(X0,k1_setfam_1(sK2))) ) | ~spl8_13),
% 1.42/0.54    inference(resolution,[],[f413,f61])).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f40])).
% 1.42/0.54  fof(f413,plain,(
% 1.42/0.54    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(sK1,X0)) ) | ~spl8_13),
% 1.42/0.54    inference(resolution,[],[f406,f55])).
% 1.42/0.54  fof(f55,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f18])).
% 1.42/0.54  fof(f18,plain,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.42/0.54    inference(ennf_transformation,[],[f10])).
% 1.42/0.54  fof(f10,axiom,(
% 1.42/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.42/0.54  fof(f406,plain,(
% 1.42/0.54    ( ! [X0] : (~r1_tarski(k1_setfam_1(sK2),X0) | r2_hidden(sK1,X0)) ) | ~spl8_13),
% 1.42/0.54    inference(resolution,[],[f355,f63])).
% 1.42/0.54  fof(f63,plain,(
% 1.42/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f44])).
% 1.42/0.54  fof(f44,plain,(
% 1.42/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 1.42/0.54  fof(f43,plain,(
% 1.42/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f42,plain,(
% 1.42/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.54    inference(rectify,[],[f41])).
% 1.42/0.54  fof(f41,plain,(
% 1.42/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.42/0.54    inference(nnf_transformation,[],[f25])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f1])).
% 1.42/0.54  fof(f1,axiom,(
% 1.42/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.42/0.54  fof(f355,plain,(
% 1.42/0.54    r2_hidden(sK1,k1_setfam_1(sK2)) | ~spl8_13),
% 1.42/0.54    inference(avatar_component_clause,[],[f354])).
% 1.42/0.54  fof(f422,plain,(
% 1.42/0.54    spl8_2 | ~spl8_3 | ~spl8_13),
% 1.42/0.54    inference(avatar_split_clause,[],[f416,f354,f79,f75])).
% 1.42/0.54  fof(f75,plain,(
% 1.42/0.54    spl8_2 <=> r2_hidden(sK1,sK3)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.42/0.54  fof(f79,plain,(
% 1.42/0.54    spl8_3 <=> r2_hidden(sK3,sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.42/0.54  fof(f416,plain,(
% 1.42/0.54    r2_hidden(sK1,sK3) | (~spl8_3 | ~spl8_13)),
% 1.42/0.54    inference(resolution,[],[f413,f80])).
% 1.42/0.54  fof(f80,plain,(
% 1.42/0.54    r2_hidden(sK3,sK2) | ~spl8_3),
% 1.42/0.54    inference(avatar_component_clause,[],[f79])).
% 1.42/0.54  fof(f404,plain,(
% 1.42/0.54    ~spl8_11),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f402])).
% 1.42/0.54  fof(f402,plain,(
% 1.42/0.54    $false | ~spl8_11),
% 1.42/0.54    inference(resolution,[],[f336,f120])).
% 1.42/0.54  fof(f120,plain,(
% 1.42/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.42/0.54    inference(resolution,[],[f118,f51])).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.42/0.54  fof(f118,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK4(X1))) | ~r2_hidden(X2,X0)) )),
% 1.42/0.54    inference(resolution,[],[f97,f54])).
% 1.42/0.54  fof(f54,plain,(
% 1.42/0.54    ( ! [X0] : (v1_xboole_0(sK4(X0))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f36])).
% 1.42/0.54  fof(f36,plain,(
% 1.42/0.54    ! [X0] : (v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f4,f35])).
% 1.42/0.54  fof(f35,plain,(
% 1.42/0.54    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 1.42/0.54  fof(f97,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r2_hidden(X2,X0)) )),
% 1.42/0.54    inference(resolution,[],[f52,f68])).
% 1.42/0.54  fof(f68,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.42/0.54    inference(ennf_transformation,[],[f2])).
% 1.42/0.54  fof(f2,axiom,(
% 1.42/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 1.42/0.54  fof(f52,plain,(
% 1.42/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f17])).
% 1.42/0.54  fof(f17,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.42/0.54  fof(f336,plain,(
% 1.42/0.54    r2_hidden(sK3,k1_xboole_0) | ~spl8_11),
% 1.42/0.54    inference(avatar_component_clause,[],[f335])).
% 1.42/0.54  fof(f335,plain,(
% 1.42/0.54    spl8_11 <=> r2_hidden(sK3,k1_xboole_0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.42/0.54  fof(f399,plain,(
% 1.42/0.54    k1_xboole_0 != sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.42/0.54    introduced(theory_tautology_sat_conflict,[])).
% 1.42/0.54  fof(f398,plain,(
% 1.42/0.54    ~spl8_16 | ~spl8_5 | spl8_12),
% 1.42/0.54    inference(avatar_split_clause,[],[f396,f339,f88,f372])).
% 1.42/0.54  fof(f372,plain,(
% 1.42/0.54    spl8_16 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.42/0.54  fof(f88,plain,(
% 1.42/0.54    spl8_5 <=> r2_hidden(sK1,sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.42/0.54  fof(f339,plain,(
% 1.42/0.54    spl8_12 <=> r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.42/0.54  fof(f396,plain,(
% 1.42/0.54    ~r2_hidden(sK1,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl8_12),
% 1.42/0.54    inference(superposition,[],[f394,f70])).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.42/0.54    inference(equality_resolution,[],[f60])).
% 1.42/0.54  fof(f60,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f22])).
% 1.42/0.54  fof(f22,plain,(
% 1.42/0.54    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(ennf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.42/0.54  fof(f394,plain,(
% 1.42/0.54    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | spl8_12),
% 1.42/0.54    inference(avatar_component_clause,[],[f339])).
% 1.42/0.54  fof(f395,plain,(
% 1.42/0.54    ~spl8_12 | spl8_1 | ~spl8_8),
% 1.42/0.54    inference(avatar_split_clause,[],[f393,f152,f72,f339])).
% 1.42/0.54  fof(f72,plain,(
% 1.42/0.54    spl8_1 <=> r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.42/0.54  fof(f393,plain,(
% 1.42/0.54    ~r2_hidden(sK1,k8_setfam_1(sK0,k1_xboole_0)) | (spl8_1 | ~spl8_8)),
% 1.42/0.54    inference(superposition,[],[f73,f153])).
% 1.42/0.54  fof(f153,plain,(
% 1.42/0.54    k1_xboole_0 = sK2 | ~spl8_8),
% 1.42/0.54    inference(avatar_component_clause,[],[f152])).
% 1.42/0.54  fof(f73,plain,(
% 1.42/0.54    ~r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | spl8_1),
% 1.42/0.54    inference(avatar_component_clause,[],[f72])).
% 1.42/0.54  fof(f389,plain,(
% 1.42/0.54    spl8_8 | spl8_18 | ~spl8_4),
% 1.42/0.54    inference(avatar_split_clause,[],[f382,f84,f387,f152])).
% 1.42/0.54  fof(f84,plain,(
% 1.42/0.54    spl8_4 <=> ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.42/0.54  fof(f382,plain,(
% 1.42/0.54    ( ! [X0] : (r2_hidden(sK1,sK6(sK2,X0)) | k1_xboole_0 = sK2 | r1_tarski(X0,k1_setfam_1(sK2))) ) | ~spl8_4),
% 1.42/0.54    inference(resolution,[],[f85,f61])).
% 1.42/0.54  fof(f85,plain,(
% 1.42/0.54    ( ! [X4] : (~r2_hidden(X4,sK2) | r2_hidden(sK1,X4)) ) | ~spl8_4),
% 1.42/0.54    inference(avatar_component_clause,[],[f84])).
% 1.42/0.54  fof(f381,plain,(
% 1.42/0.54    ~spl8_13 | spl8_1 | ~spl8_10),
% 1.42/0.54    inference(avatar_split_clause,[],[f361,f304,f72,f354])).
% 1.42/0.54  fof(f304,plain,(
% 1.42/0.54    spl8_10 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.42/0.54  fof(f361,plain,(
% 1.42/0.54    ~r2_hidden(sK1,k1_setfam_1(sK2)) | (spl8_1 | ~spl8_10)),
% 1.42/0.54    inference(forward_demodulation,[],[f73,f305])).
% 1.42/0.54  fof(f305,plain,(
% 1.42/0.54    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl8_10),
% 1.42/0.54    inference(avatar_component_clause,[],[f304])).
% 1.42/0.54  fof(f356,plain,(
% 1.42/0.54    spl8_13 | ~spl8_1 | ~spl8_10),
% 1.42/0.54    inference(avatar_split_clause,[],[f342,f304,f72,f354])).
% 1.42/0.54  fof(f342,plain,(
% 1.42/0.54    r2_hidden(sK1,k1_setfam_1(sK2)) | (~spl8_1 | ~spl8_10)),
% 1.42/0.54    inference(superposition,[],[f82,f305])).
% 1.42/0.54  fof(f82,plain,(
% 1.42/0.54    r2_hidden(sK1,k8_setfam_1(sK0,sK2)) | ~spl8_1),
% 1.42/0.54    inference(avatar_component_clause,[],[f72])).
% 1.42/0.54  fof(f337,plain,(
% 1.42/0.54    spl8_11 | ~spl8_3 | ~spl8_8),
% 1.42/0.54    inference(avatar_split_clause,[],[f307,f152,f79,f335])).
% 1.42/0.54  fof(f307,plain,(
% 1.42/0.54    r2_hidden(sK3,k1_xboole_0) | (~spl8_3 | ~spl8_8)),
% 1.42/0.54    inference(superposition,[],[f80,f153])).
% 1.42/0.54  fof(f306,plain,(
% 1.42/0.54    spl8_10 | spl8_8 | ~spl8_6),
% 1.42/0.54    inference(avatar_split_clause,[],[f298,f92,f152,f304])).
% 1.42/0.54  fof(f92,plain,(
% 1.42/0.54    spl8_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.42/0.54  fof(f298,plain,(
% 1.42/0.54    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl8_6),
% 1.42/0.54    inference(resolution,[],[f227,f93])).
% 1.42/0.54  fof(f93,plain,(
% 1.42/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl8_6),
% 1.42/0.54    inference(avatar_component_clause,[],[f92])).
% 1.42/0.54  fof(f227,plain,(
% 1.42/0.54    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f224])).
% 1.42/0.54  fof(f224,plain,(
% 1.42/0.54    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 1.42/0.54    inference(superposition,[],[f59,f58])).
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f21])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(ennf_transformation,[],[f9])).
% 1.42/0.54  fof(f9,axiom,(
% 1.42/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.42/0.54  fof(f59,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f22])).
% 1.42/0.54  fof(f94,plain,(
% 1.42/0.54    spl8_6),
% 1.42/0.54    inference(avatar_split_clause,[],[f46,f92])).
% 1.42/0.54  fof(f46,plain,(
% 1.42/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  % (21420)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.54  fof(f34,plain,(
% 1.42/0.54    ((~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f33,f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & (! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2)) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) & r2_hidden(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ? [X3] : (~r2_hidden(sK1,X3) & r2_hidden(X3,sK2)) => (~r2_hidden(sK1,sK3) & r2_hidden(sK3,sK2))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f31,plain,(
% 1.42/0.54    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X4] : (r2_hidden(X1,X4) | ~r2_hidden(X4,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(rectify,[],[f30])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ? [X0,X1,X2] : ((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(flattening,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (((? [X3] : (~r2_hidden(X1,X3) & r2_hidden(X3,X2)) | ~r2_hidden(X1,k8_setfam_1(X0,X2))) & (! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2)) | r2_hidden(X1,k8_setfam_1(X0,X2)))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(nnf_transformation,[],[f16])).
% 1.42/0.54  fof(f16,plain,(
% 1.42/0.54    ? [X0,X1,X2] : ((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(flattening,[],[f15])).
% 1.42/0.54  fof(f15,plain,(
% 1.42/0.54    ? [X0,X1,X2] : (((r2_hidden(X1,k8_setfam_1(X0,X2)) <~> ! [X3] : (r2_hidden(X1,X3) | ~r2_hidden(X3,X2))) & r2_hidden(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.42/0.54    inference(ennf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,negated_conjecture,(
% 1.42/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 1.42/0.54    inference(negated_conjecture,[],[f13])).
% 1.42/0.54  fof(f13,conjecture,(
% 1.42/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r2_hidden(X1,X0) => (r2_hidden(X1,k8_setfam_1(X0,X2)) <=> ! [X3] : (r2_hidden(X3,X2) => r2_hidden(X1,X3)))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_setfam_1)).
% 1.42/0.54  fof(f90,plain,(
% 1.42/0.54    spl8_5),
% 1.42/0.54    inference(avatar_split_clause,[],[f47,f88])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    r2_hidden(sK1,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  fof(f86,plain,(
% 1.42/0.54    spl8_1 | spl8_4),
% 1.42/0.54    inference(avatar_split_clause,[],[f48,f84,f72])).
% 1.42/0.54  fof(f48,plain,(
% 1.42/0.54    ( ! [X4] : (r2_hidden(sK1,X4) | ~r2_hidden(X4,sK2) | r2_hidden(sK1,k8_setfam_1(sK0,sK2))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  fof(f81,plain,(
% 1.42/0.54    ~spl8_1 | spl8_3),
% 1.42/0.54    inference(avatar_split_clause,[],[f49,f79,f72])).
% 1.42/0.54  fof(f49,plain,(
% 1.42/0.54    r2_hidden(sK3,sK2) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  fof(f77,plain,(
% 1.42/0.54    ~spl8_1 | ~spl8_2),
% 1.42/0.54    inference(avatar_split_clause,[],[f50,f75,f72])).
% 1.42/0.54  fof(f50,plain,(
% 1.42/0.54    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,k8_setfam_1(sK0,sK2))),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (21419)------------------------------
% 1.42/0.54  % (21419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (21419)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (21419)Memory used [KB]: 11001
% 1.42/0.54  % (21419)Time elapsed: 0.153 s
% 1.42/0.54  % (21419)------------------------------
% 1.42/0.54  % (21419)------------------------------
% 1.42/0.54  % (21426)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (21398)Success in time 0.192 s
%------------------------------------------------------------------------------
