%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:40 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 263 expanded)
%              Number of leaves         :   29 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 ( 725 expanded)
%              Number of equality atoms :   69 ( 185 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f77,f80,f88,f100,f134,f293,f298,f358,f361,f371,f378,f394,f399,f1221])).

fof(f1221,plain,
    ( spl3_15
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f1197])).

fof(f1197,plain,
    ( $false
    | spl3_15
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f393,f398,f1085])).

fof(f1085,plain,(
    ! [X21,X22] :
      ( ~ r1_tarski(k5_xboole_0(X21,X22),X22)
      | r1_tarski(X21,X22) ) ),
    inference(superposition,[],[f1051,f213])).

fof(f213,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f181,f181])).

fof(f181,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f162,f41])).

fof(f41,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f162,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f149,f101])).

fof(f101,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f41,f56])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f149,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f37,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1051,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X6,k5_xboole_0(X6,X5))
      | r1_tarski(X5,k5_xboole_0(X6,X5)) ) ),
    inference(resolution,[],[f188,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      | r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f43,f162])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f398,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl3_16
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f393,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl3_15
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f399,plain,
    ( ~ spl3_12
    | spl3_16
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f363,f70,f396,f375])).

fof(f375,plain,
    ( spl3_12
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f70,plain,
    ( spl3_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f363,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f72,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f138,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f59,f114])).

fof(f114,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X2
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f48,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f138,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(global_subsumption,[],[f54,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f51,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f72,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f394,plain,
    ( ~ spl3_15
    | spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f388,f375,f84,f391])).

fof(f84,plain,
    ( spl3_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f388,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK0,sK1)
    | ~ spl3_12 ),
    inference(resolution,[],[f377,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f377,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f375])).

fof(f378,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f372,f368,f375])).

fof(f368,plain,
    ( spl3_11
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f372,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_11 ),
    inference(resolution,[],[f370,f63])).

fof(f63,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f370,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f368])).

fof(f371,plain,
    ( spl3_7
    | spl3_11
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f118,f65,f368,f123])).

fof(f123,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f118,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f361,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f360,f74,f84])).

fof(f74,plain,
    ( spl3_3
  <=> sK1 = k2_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f360,plain,
    ( sK0 != sK1
    | spl3_3 ),
    inference(forward_demodulation,[],[f75,f42])).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f75,plain,
    ( sK1 != k2_subset_1(sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f358,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f355])).

fof(f355,plain,
    ( $false
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f173,f292])).

fof(f292,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl3_10
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f173,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f172,f60])).

fof(f172,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_tarski(k1_xboole_0,X3) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_xboole_0,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f43,f57])).

fof(f298,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f60,f288])).

fof(f288,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f286])).

fof(f286,plain,
    ( spl3_9
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f293,plain,
    ( ~ spl3_9
    | ~ spl3_10
    | spl3_6 ),
    inference(avatar_split_clause,[],[f284,f97,f290,f286])).

fof(f97,plain,
    ( spl3_6
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f284,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ r1_tarski(sK0,sK0)
    | spl3_6 ),
    inference(forward_demodulation,[],[f280,f57])).

fof(f280,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK0),sK0)
    | ~ r1_tarski(sK0,sK0)
    | spl3_6 ),
    inference(superposition,[],[f99,f206])).

fof(f99,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f134,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f54,f125])).

fof(f125,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f100,plain,
    ( ~ spl3_6
    | spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f84,f70,f97])).

fof(f89,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f71,f86])).

fof(f86,plain,
    ( sK0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f71,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f88,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f82,f74,f84])).

fof(f82,plain,
    ( sK0 = sK1
    | ~ spl3_3 ),
    inference(superposition,[],[f76,f42])).

fof(f76,plain,
    ( sK1 = k2_subset_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f80,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f79,f74,f70])).

fof(f79,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f78])).

fof(f78,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f36,f76])).

fof(f36,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f77,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f35,f74,f70])).

fof(f35,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f68,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:19:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (4855)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (4867)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (4875)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (4876)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (4868)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (4858)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (4867)Refutation not found, incomplete strategy% (4867)------------------------------
% 0.22/0.55  % (4867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (4867)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (4867)Memory used [KB]: 1791
% 0.22/0.55  % (4867)Time elapsed: 0.125 s
% 0.22/0.55  % (4867)------------------------------
% 0.22/0.55  % (4867)------------------------------
% 0.22/0.56  % (4865)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (4882)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.58  % (4882)Refutation not found, incomplete strategy% (4882)------------------------------
% 0.22/0.58  % (4882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (4882)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (4882)Memory used [KB]: 1663
% 0.22/0.58  % (4882)Time elapsed: 0.002 s
% 0.22/0.58  % (4882)------------------------------
% 0.22/0.58  % (4882)------------------------------
% 0.22/0.58  % (4865)Refutation not found, incomplete strategy% (4865)------------------------------
% 0.22/0.58  % (4865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (4865)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (4865)Memory used [KB]: 10618
% 0.22/0.58  % (4865)Time elapsed: 0.149 s
% 0.22/0.58  % (4865)------------------------------
% 0.22/0.58  % (4865)------------------------------
% 1.62/0.59  % (4876)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f1222,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(avatar_sat_refutation,[],[f68,f77,f80,f88,f100,f134,f293,f298,f358,f361,f371,f378,f394,f399,f1221])).
% 1.62/0.59  fof(f1221,plain,(
% 1.62/0.59    spl3_15 | ~spl3_16),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f1197])).
% 1.62/0.59  fof(f1197,plain,(
% 1.62/0.59    $false | (spl3_15 | ~spl3_16)),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f393,f398,f1085])).
% 1.62/0.59  fof(f1085,plain,(
% 1.62/0.59    ( ! [X21,X22] : (~r1_tarski(k5_xboole_0(X21,X22),X22) | r1_tarski(X21,X22)) )),
% 1.62/0.59    inference(superposition,[],[f1051,f213])).
% 1.62/0.59  fof(f213,plain,(
% 1.62/0.59    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 1.62/0.59    inference(superposition,[],[f181,f181])).
% 1.62/0.59  fof(f181,plain,(
% 1.62/0.59    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.62/0.59    inference(superposition,[],[f162,f41])).
% 1.62/0.59  fof(f41,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.62/0.59  fof(f162,plain,(
% 1.62/0.59    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.62/0.59    inference(forward_demodulation,[],[f149,f101])).
% 1.62/0.59  fof(f101,plain,(
% 1.62/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.62/0.59    inference(superposition,[],[f41,f56])).
% 1.62/0.59  fof(f56,plain,(
% 1.62/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.62/0.59  fof(f149,plain,(
% 1.62/0.59    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.62/0.59    inference(superposition,[],[f37,f57])).
% 1.62/0.59  fof(f57,plain,(
% 1.62/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f9])).
% 1.62/0.59  fof(f9,axiom,(
% 1.62/0.59    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.62/0.59  fof(f1051,plain,(
% 1.62/0.59    ( ! [X6,X5] : (~r1_tarski(X6,k5_xboole_0(X6,X5)) | r1_tarski(X5,k5_xboole_0(X6,X5))) )),
% 1.62/0.59    inference(resolution,[],[f188,f60])).
% 1.62/0.59  fof(f60,plain,(
% 1.62/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.62/0.59    inference(equality_resolution,[],[f39])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.59    inference(flattening,[],[f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f3])).
% 1.62/0.59  fof(f3,axiom,(
% 1.62/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.59  fof(f188,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (~r1_tarski(k5_xboole_0(X0,X1),X2) | r1_tarski(X1,X2) | ~r1_tarski(X0,X2)) )),
% 1.62/0.59    inference(superposition,[],[f43,f162])).
% 1.62/0.59  fof(f43,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.62/0.59    inference(flattening,[],[f18])).
% 1.62/0.59  fof(f18,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.62/0.59    inference(ennf_transformation,[],[f5])).
% 1.62/0.59  fof(f5,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.62/0.59  fof(f398,plain,(
% 1.62/0.59    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~spl3_16),
% 1.62/0.59    inference(avatar_component_clause,[],[f396])).
% 1.62/0.59  fof(f396,plain,(
% 1.62/0.59    spl3_16 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.62/0.59  fof(f393,plain,(
% 1.62/0.59    ~r1_tarski(sK0,sK1) | spl3_15),
% 1.62/0.59    inference(avatar_component_clause,[],[f391])).
% 1.62/0.59  fof(f391,plain,(
% 1.62/0.59    spl3_15 <=> r1_tarski(sK0,sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.62/0.59  fof(f399,plain,(
% 1.62/0.59    ~spl3_12 | spl3_16 | ~spl3_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f363,f70,f396,f375])).
% 1.62/0.59  fof(f375,plain,(
% 1.62/0.59    spl3_12 <=> r1_tarski(sK1,sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.62/0.59  fof(f70,plain,(
% 1.62/0.59    spl3_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.62/0.59  fof(f363,plain,(
% 1.62/0.59    r1_tarski(k5_xboole_0(sK0,sK1),sK1) | ~r1_tarski(sK1,sK0) | ~spl3_2),
% 1.62/0.59    inference(superposition,[],[f72,f206])).
% 1.62/0.59  fof(f206,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.62/0.59    inference(global_subsumption,[],[f138,f195])).
% 1.62/0.59  fof(f195,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 1.62/0.59    inference(superposition,[],[f59,f114])).
% 1.62/0.59  fof(f114,plain,(
% 1.62/0.59    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) )),
% 1.62/0.59    inference(superposition,[],[f48,f58])).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.62/0.59  fof(f48,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.62/0.59    inference(ennf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(definition_unfolding,[],[f49,f55])).
% 1.62/0.59  fof(f55,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.59  fof(f49,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,axiom,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.62/0.59  fof(f138,plain,(
% 1.62/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(global_subsumption,[],[f54,f136])).
% 1.62/0.59  fof(f136,plain,(
% 1.62/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(resolution,[],[f51,f62])).
% 1.62/0.59  fof(f62,plain,(
% 1.62/0.59    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.62/0.59    inference(equality_resolution,[],[f45])).
% 1.62/0.59  fof(f45,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f32])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.62/0.59    inference(rectify,[],[f29])).
% 1.62/0.59  fof(f29,plain,(
% 1.62/0.59    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,axiom,(
% 1.62/0.59    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f33])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.62/0.59    inference(nnf_transformation,[],[f22])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,axiom,(
% 1.62/0.59    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.62/0.59  fof(f54,plain,(
% 1.62/0.59    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f14])).
% 1.62/0.59  fof(f14,axiom,(
% 1.62/0.59    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.62/0.59  fof(f72,plain,(
% 1.62/0.59    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_2),
% 1.62/0.59    inference(avatar_component_clause,[],[f70])).
% 1.62/0.59  fof(f394,plain,(
% 1.62/0.59    ~spl3_15 | spl3_4 | ~spl3_12),
% 1.62/0.59    inference(avatar_split_clause,[],[f388,f375,f84,f391])).
% 1.62/0.59  fof(f84,plain,(
% 1.62/0.59    spl3_4 <=> sK0 = sK1),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.62/0.59  fof(f388,plain,(
% 1.62/0.59    sK0 = sK1 | ~r1_tarski(sK0,sK1) | ~spl3_12),
% 1.62/0.59    inference(resolution,[],[f377,f40])).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f28])).
% 1.62/0.59  fof(f377,plain,(
% 1.62/0.59    r1_tarski(sK1,sK0) | ~spl3_12),
% 1.62/0.59    inference(avatar_component_clause,[],[f375])).
% 1.62/0.59  fof(f378,plain,(
% 1.62/0.59    spl3_12 | ~spl3_11),
% 1.62/0.59    inference(avatar_split_clause,[],[f372,f368,f375])).
% 1.62/0.59  fof(f368,plain,(
% 1.62/0.59    spl3_11 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.62/0.59  fof(f372,plain,(
% 1.62/0.59    r1_tarski(sK1,sK0) | ~spl3_11),
% 1.62/0.59    inference(resolution,[],[f370,f63])).
% 1.62/0.59  fof(f63,plain,(
% 1.62/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 1.62/0.59    inference(equality_resolution,[],[f44])).
% 1.62/0.59  fof(f44,plain,(
% 1.62/0.59    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.62/0.59    inference(cnf_transformation,[],[f32])).
% 1.62/0.59  fof(f370,plain,(
% 1.62/0.59    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_11),
% 1.62/0.59    inference(avatar_component_clause,[],[f368])).
% 1.62/0.59  fof(f371,plain,(
% 1.62/0.59    spl3_7 | spl3_11 | ~spl3_1),
% 1.62/0.59    inference(avatar_split_clause,[],[f118,f65,f368,f123])).
% 1.62/0.59  fof(f123,plain,(
% 1.62/0.59    spl3_7 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.62/0.59  fof(f118,plain,(
% 1.62/0.59    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.62/0.59    inference(resolution,[],[f50,f67])).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f65])).
% 1.62/0.59  fof(f50,plain,(
% 1.62/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f33])).
% 1.62/0.59  fof(f361,plain,(
% 1.62/0.59    ~spl3_4 | spl3_3),
% 1.62/0.59    inference(avatar_split_clause,[],[f360,f74,f84])).
% 1.62/0.59  fof(f74,plain,(
% 1.62/0.59    spl3_3 <=> sK1 = k2_subset_1(sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.62/0.59  fof(f360,plain,(
% 1.62/0.59    sK0 != sK1 | spl3_3),
% 1.62/0.59    inference(forward_demodulation,[],[f75,f42])).
% 1.62/0.59  fof(f42,plain,(
% 1.62/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.62/0.59    inference(cnf_transformation,[],[f12])).
% 1.62/0.59  fof(f12,axiom,(
% 1.62/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.62/0.59  fof(f75,plain,(
% 1.62/0.59    sK1 != k2_subset_1(sK0) | spl3_3),
% 1.62/0.59    inference(avatar_component_clause,[],[f74])).
% 1.62/0.59  fof(f358,plain,(
% 1.62/0.59    spl3_10),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f355])).
% 1.62/0.59  fof(f355,plain,(
% 1.62/0.59    $false | spl3_10),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f173,f292])).
% 1.62/0.59  fof(f292,plain,(
% 1.62/0.59    ~r1_tarski(k1_xboole_0,sK0) | spl3_10),
% 1.62/0.59    inference(avatar_component_clause,[],[f290])).
% 1.62/0.59  fof(f290,plain,(
% 1.62/0.59    spl3_10 <=> r1_tarski(k1_xboole_0,sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.62/0.59  fof(f173,plain,(
% 1.62/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.59    inference(resolution,[],[f172,f60])).
% 1.62/0.59  fof(f172,plain,(
% 1.62/0.59    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k1_xboole_0,X3)) )),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f167])).
% 1.62/0.59  fof(f167,plain,(
% 1.62/0.59    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X2,X3)) )),
% 1.62/0.59    inference(superposition,[],[f43,f57])).
% 1.62/0.59  fof(f298,plain,(
% 1.62/0.59    spl3_9),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f294])).
% 1.62/0.59  fof(f294,plain,(
% 1.62/0.59    $false | spl3_9),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f60,f288])).
% 1.62/0.59  fof(f288,plain,(
% 1.62/0.59    ~r1_tarski(sK0,sK0) | spl3_9),
% 1.62/0.59    inference(avatar_component_clause,[],[f286])).
% 1.62/0.59  fof(f286,plain,(
% 1.62/0.59    spl3_9 <=> r1_tarski(sK0,sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.62/0.59  fof(f293,plain,(
% 1.62/0.59    ~spl3_9 | ~spl3_10 | spl3_6),
% 1.62/0.59    inference(avatar_split_clause,[],[f284,f97,f290,f286])).
% 1.62/0.59  fof(f97,plain,(
% 1.62/0.59    spl3_6 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.62/0.59  fof(f284,plain,(
% 1.62/0.59    ~r1_tarski(k1_xboole_0,sK0) | ~r1_tarski(sK0,sK0) | spl3_6),
% 1.62/0.59    inference(forward_demodulation,[],[f280,f57])).
% 1.62/0.59  fof(f280,plain,(
% 1.62/0.59    ~r1_tarski(k5_xboole_0(sK0,sK0),sK0) | ~r1_tarski(sK0,sK0) | spl3_6),
% 1.62/0.59    inference(superposition,[],[f99,f206])).
% 1.62/0.59  fof(f99,plain,(
% 1.62/0.59    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl3_6),
% 1.62/0.59    inference(avatar_component_clause,[],[f97])).
% 1.62/0.59  fof(f134,plain,(
% 1.62/0.59    ~spl3_7),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f131])).
% 1.62/0.59  fof(f131,plain,(
% 1.62/0.59    $false | ~spl3_7),
% 1.62/0.59    inference(unit_resulting_resolution,[],[f54,f125])).
% 1.62/0.59  fof(f125,plain,(
% 1.62/0.59    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_7),
% 1.62/0.59    inference(avatar_component_clause,[],[f123])).
% 1.62/0.59  fof(f100,plain,(
% 1.62/0.59    ~spl3_6 | spl3_2 | ~spl3_4),
% 1.62/0.59    inference(avatar_split_clause,[],[f89,f84,f70,f97])).
% 1.62/0.59  fof(f89,plain,(
% 1.62/0.59    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl3_2 | ~spl3_4)),
% 1.62/0.59    inference(superposition,[],[f71,f86])).
% 1.62/0.59  fof(f86,plain,(
% 1.62/0.59    sK0 = sK1 | ~spl3_4),
% 1.62/0.59    inference(avatar_component_clause,[],[f84])).
% 1.62/0.59  fof(f71,plain,(
% 1.62/0.59    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl3_2),
% 1.62/0.59    inference(avatar_component_clause,[],[f70])).
% 1.62/0.59  fof(f88,plain,(
% 1.62/0.59    spl3_4 | ~spl3_3),
% 1.62/0.59    inference(avatar_split_clause,[],[f82,f74,f84])).
% 1.62/0.59  fof(f82,plain,(
% 1.62/0.59    sK0 = sK1 | ~spl3_3),
% 1.62/0.59    inference(superposition,[],[f76,f42])).
% 1.62/0.59  fof(f76,plain,(
% 1.62/0.59    sK1 = k2_subset_1(sK0) | ~spl3_3),
% 1.62/0.59    inference(avatar_component_clause,[],[f74])).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    ~spl3_2 | ~spl3_3),
% 1.62/0.59    inference(avatar_split_clause,[],[f79,f74,f70])).
% 1.62/0.59  fof(f79,plain,(
% 1.62/0.59    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_3),
% 1.62/0.59    inference(trivial_inequality_removal,[],[f78])).
% 1.62/0.59  fof(f78,plain,(
% 1.62/0.59    sK1 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl3_3),
% 1.62/0.59    inference(forward_demodulation,[],[f36,f76])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(flattening,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(nnf_transformation,[],[f17])).
% 1.62/0.59  fof(f17,plain,(
% 1.62/0.59    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f16])).
% 1.62/0.59  fof(f16,negated_conjecture,(
% 1.62/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.62/0.59    inference(negated_conjecture,[],[f15])).
% 1.62/0.59  fof(f15,conjecture,(
% 1.62/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.62/0.59  fof(f77,plain,(
% 1.62/0.59    spl3_2 | spl3_3),
% 1.62/0.59    inference(avatar_split_clause,[],[f35,f74,f70])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  fof(f68,plain,(
% 1.62/0.59    spl3_1),
% 1.62/0.59    inference(avatar_split_clause,[],[f34,f65])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.62/0.59    inference(cnf_transformation,[],[f26])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (4876)------------------------------
% 1.62/0.59  % (4876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (4876)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (4876)Memory used [KB]: 11769
% 1.62/0.59  % (4876)Time elapsed: 0.077 s
% 1.62/0.59  % (4876)------------------------------
% 1.62/0.59  % (4876)------------------------------
% 1.62/0.59  % (4852)Success in time 0.223 s
%------------------------------------------------------------------------------
