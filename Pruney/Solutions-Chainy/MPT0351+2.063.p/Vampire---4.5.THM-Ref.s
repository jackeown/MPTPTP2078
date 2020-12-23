%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 224 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  217 ( 407 expanded)
%              Number of equality atoms :   71 ( 172 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f181,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f67,f80,f82,f88,f109,f164,f170,f178,f180])).

fof(f180,plain,
    ( sK0 != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | k4_subset_1(sK0,sK0,sK1) != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | k4_subset_1(sK0,sK1,sK0) != k4_subset_1(sK0,sK0,sK1)
    | sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f178,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f174,f168,f176])).

fof(f176,plain,
    ( spl3_17
  <=> sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f168,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f174,plain,
    ( sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f171,f51])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f171,plain,
    ( k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k1_xboole_0))
    | ~ spl3_16 ),
    inference(superposition,[],[f52,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f50,f50])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f170,plain,
    ( spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f166,f161,f168])).

fof(f161,plain,
    ( spl3_15
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f166,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl3_15 ),
    inference(resolution,[],[f162,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f162,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f164,plain,
    ( spl3_15
    | spl3_5
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f159,f107,f59,f78,f161])).

fof(f78,plain,
    ( spl3_5
  <=> sK0 = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f59,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f107,plain,
    ( spl3_8
  <=> k4_subset_1(sK0,sK0,sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f159,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | r1_tarski(sK1,sK0)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f156,f108])).

fof(f108,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f156,plain,
    ( sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | r1_tarski(sK1,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f154,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f154,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(X0,sK0),sK1)
        | sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f93,f60])).

fof(f60,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f93,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X1))
      | ~ r2_hidden(sK2(X2,X1),X3)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X1 ) ),
    inference(resolution,[],[f91,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1 ) ),
    inference(forward_demodulation,[],[f90,f51])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0))
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(superposition,[],[f52,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(resolution,[],[f43,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f109,plain,
    ( spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f101,f59,f107])).

fof(f101,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f34,f32])).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f98,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,X0,sK1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,sK1)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f53,f60])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f88,plain,
    ( spl3_6
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f83,f59,f86])).

fof(f86,plain,
    ( spl3_6
  <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f83,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f72,f60])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2) ) ),
    inference(resolution,[],[f46,f62])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f76,f62])).

fof(f76,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_4
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f80,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f73,f65,f59,f78,f75])).

fof(f65,plain,
    ( spl3_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f73,plain,
    ( sK0 != k4_subset_1(sK0,sK0,sK1)
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_2
    | spl3_3 ),
    inference(superposition,[],[f66,f71])).

fof(f71,plain,
    ( ! [X0] :
        ( k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f60])).

fof(f66,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f63,f55,f65])).

fof(f55,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f56,f32])).

fof(f56,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f61,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f57,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (14578)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (14578)Refutation not found, incomplete strategy% (14578)------------------------------
% 0.20/0.49  % (14578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14578)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (14578)Memory used [KB]: 6140
% 0.20/0.49  % (14578)Time elapsed: 0.090 s
% 0.20/0.49  % (14578)------------------------------
% 0.20/0.49  % (14578)------------------------------
% 0.20/0.49  % (14597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (14593)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (14576)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (14593)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f57,f61,f67,f80,f82,f88,f109,f164,f170,f178,f180])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    sK0 != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | k4_subset_1(sK0,sK0,sK1) != k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | k4_subset_1(sK0,sK1,sK0) != k4_subset_1(sK0,sK0,sK1) | sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    spl3_17 | ~spl3_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f174,f168,f176])).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    spl3_17 <=> sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    spl3_16 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl3_16),
% 0.20/0.51    inference(forward_demodulation,[],[f171,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f33,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f44,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k1_xboole_0)) | ~spl3_16),
% 0.20/0.51    inference(superposition,[],[f52,f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_16),
% 0.20/0.51    inference(avatar_component_clause,[],[f168])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f37,f50,f50])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl3_16 | ~spl3_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f166,f161,f168])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl3_15 <=> r1_tarski(sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl3_15),
% 0.20/0.51    inference(resolution,[],[f162,f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.51    inference(nnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    r1_tarski(sK1,sK0) | ~spl3_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f161])).
% 0.20/0.51  fof(f164,plain,(
% 0.20/0.51    spl3_15 | spl3_5 | ~spl3_2 | ~spl3_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f159,f107,f59,f78,f161])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    spl3_5 <=> sK0 = k4_subset_1(sK0,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl3_8 <=> k4_subset_1(sK0,sK0,sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.51  fof(f159,plain,(
% 0.20/0.51    sK0 = k4_subset_1(sK0,sK0,sK1) | r1_tarski(sK1,sK0) | (~spl3_2 | ~spl3_8)),
% 0.20/0.51    inference(forward_demodulation,[],[f156,f108])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl3_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f107])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | r1_tarski(sK1,sK0) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f154,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f154,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK2(X0,sK0),sK1) | sK0 = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,X0))) ) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f93,f60])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f59])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~r2_hidden(sK2(X2,X1),X3) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) = X1) )),
% 0.20/0.51    inference(resolution,[],[f91,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = X1) )),
% 0.20/0.51    inference(forward_demodulation,[],[f90,f51])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,k1_xboole_0)) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.51    inference(superposition,[],[f52,f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.51    inference(resolution,[],[f43,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl3_8 | ~spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f101,f59,f107])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f98,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f34,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,sK1))) ) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f53,f60])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f45,f50])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl3_6 | ~spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f83,f59,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    spl3_6 <=> k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f72,f60])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | k4_subset_1(X1,X2,X1) = k4_subset_1(X1,X1,X2)) )),
% 0.20/0.51    inference(resolution,[],[f46,f62])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl3_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    $false | spl3_4),
% 0.20/0.51    inference(resolution,[],[f76,f62])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f75])).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    spl3_4 <=> m1_subset_1(sK0,k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ~spl3_4 | ~spl3_5 | ~spl3_2 | spl3_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f73,f65,f59,f78,f75])).
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    spl3_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    sK0 != k4_subset_1(sK0,sK0,sK1) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | (~spl3_2 | spl3_3)),
% 0.20/0.51    inference(superposition,[],[f66,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X0] : (k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) ) | ~spl3_2),
% 0.20/0.51    inference(resolution,[],[f46,f60])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f65])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ~spl3_3 | spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f63,f55,f65])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl3_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    sK0 != k4_subset_1(sK0,sK1,sK0) | spl3_1),
% 0.20/0.51    inference(forward_demodulation,[],[f56,f32])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f55])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f59])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f14])).
% 0.20/0.51  fof(f14,conjecture,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ~spl3_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f55])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (14593)------------------------------
% 0.20/0.51  % (14593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (14593)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (14593)Memory used [KB]: 10874
% 0.20/0.51  % (14593)Time elapsed: 0.112 s
% 0.20/0.51  % (14593)------------------------------
% 0.20/0.51  % (14593)------------------------------
% 0.20/0.51  % (14571)Success in time 0.153 s
%------------------------------------------------------------------------------
