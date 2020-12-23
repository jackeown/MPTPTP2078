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
% DateTime   : Thu Dec  3 12:44:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 234 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   10
%              Number of atoms          :  232 ( 459 expanded)
%              Number of equality atoms :   88 ( 192 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f73,f77,f84,f93,f261,f274,f278,f281,f288,f294,f313,f325,f347,f369,f385,f420,f421])).

fof(f421,plain,
    ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f420,plain,
    ( spl2_4
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f419,f399,f82])).

fof(f82,plain,
    ( spl2_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f399,plain,
    ( spl2_25
  <=> sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f419,plain,
    ( sK0 = sK1
    | ~ spl2_25 ),
    inference(forward_demodulation,[],[f400,f270])).

fof(f270,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f263,f256])).

fof(f256,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f249,f115])).

fof(f115,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f96,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f47,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f96,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f249,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f52,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f263,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f53,f78])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f400,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f399])).

fof(f385,plain,(
    spl2_20 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | spl2_20 ),
    inference(resolution,[],[f368,f44])).

fof(f368,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | spl2_20 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl2_20
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f369,plain,
    ( spl2_19
    | ~ spl2_20
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f358,f345,f367,f364])).

fof(f364,plain,
    ( spl2_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f345,plain,
    ( spl2_18
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f358,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_18 ),
    inference(superposition,[],[f55,f346])).

fof(f346,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f345])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f347,plain,
    ( spl2_18
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f333,f322,f345])).

fof(f322,plain,
    ( spl2_16
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f333,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_16 ),
    inference(superposition,[],[f111,f323])).

fof(f323,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f322])).

fof(f111,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1 ),
    inference(superposition,[],[f61,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f325,plain,
    ( spl2_16
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f316,f311,f322])).

fof(f311,plain,
    ( spl2_15
  <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f316,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl2_15 ),
    inference(superposition,[],[f50,f312])).

fof(f312,plain,
    ( sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f311])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f313,plain,
    ( spl2_15
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f309,f292,f311])).

fof(f292,plain,
    ( spl2_13
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f309,plain,
    ( sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f308,f128])).

fof(f128,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f127,f46])).

fof(f127,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f121,f43])).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f121,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f50,f115])).

fof(f308,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,sK1)
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f302,f46])).

fof(f302,plain,
    ( k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl2_13 ),
    inference(superposition,[],[f50,f293])).

fof(f293,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f292])).

fof(f294,plain,
    ( spl2_13
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f290,f276,f65,f292])).

fof(f65,plain,
    ( spl2_1
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f276,plain,
    ( spl2_11
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f290,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)
    | ~ spl2_1
    | ~ spl2_11 ),
    inference(forward_demodulation,[],[f289,f277])).

fof(f277,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f276])).

fof(f289,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f71,f57])).

fof(f71,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f288,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f260,f40])).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f260,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl2_8
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f281,plain,
    ( ~ spl2_4
    | spl2_2 ),
    inference(avatar_split_clause,[],[f279,f68,f82])).

fof(f68,plain,
    ( spl2_2
  <=> sK1 = k2_subset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f279,plain,
    ( sK0 != sK1
    | spl2_2 ),
    inference(forward_demodulation,[],[f69,f41])).

fof(f69,plain,
    ( sK1 != k2_subset_1(sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f278,plain,
    ( spl2_11
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f248,f75,f276])).

fof(f75,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f248,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f52,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f274,plain,
    ( spl2_10
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f262,f75,f272])).

fof(f272,plain,
    ( spl2_10
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f262,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_3 ),
    inference(resolution,[],[f53,f76])).

fof(f261,plain,
    ( ~ spl2_8
    | spl2_6 ),
    inference(avatar_split_clause,[],[f257,f91,f259])).

fof(f91,plain,
    ( spl2_6
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f257,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_6 ),
    inference(superposition,[],[f92,f256])).

fof(f92,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f93,plain,
    ( ~ spl2_6
    | spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f89,f82,f65,f91])).

fof(f89,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_1
    | ~ spl2_4 ),
    inference(superposition,[],[f66,f83])).

fof(f83,plain,
    ( sK0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f66,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f84,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f80,f68,f82])).

fof(f80,plain,
    ( sK0 = sK1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f72,f41])).

fof(f72,plain,
    ( sK1 = k2_subset_1(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f37,f75])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).

fof(f34,plain,
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

fof(f33,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f73,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f38,f68,f65])).

fof(f38,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f39,f68,f65])).

fof(f39,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:17:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (15034)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.49  % (15016)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (15017)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (15026)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (15011)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (15009)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (15008)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (15035)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (15029)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (15036)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (15015)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (15021)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (15026)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f422,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f70,f73,f77,f84,f93,f261,f274,f278,f281,f288,f294,f313,f325,f347,f369,f385,f420,f421])).
% 0.21/0.52  fof(f421,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) | k1_xboole_0 != k4_xboole_0(sK0,sK1) | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | sK1 = k3_subset_1(sK0,k1_xboole_0)),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f420,plain,(
% 0.21/0.52    spl2_4 | ~spl2_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f419,f399,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl2_4 <=> sK0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    spl2_25 <=> sK1 = k3_subset_1(sK0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.52  fof(f419,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl2_25),
% 0.21/0.52    inference(forward_demodulation,[],[f400,f270])).
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f263,f256])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f249,f115])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.21/0.52    inference(superposition,[],[f96,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f47,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 0.21/0.52    inference(resolution,[],[f57,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f249,plain,(
% 0.21/0.52    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f52,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f42,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 0.21/0.52    inference(resolution,[],[f53,f78])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k1_xboole_0) | ~spl2_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f399])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    spl2_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    $false | spl2_20),
% 0.21/0.52    inference(resolution,[],[f368,f44])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | spl2_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f367])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    spl2_20 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    spl2_19 | ~spl2_20 | ~spl2_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f358,f345,f367,f364])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    spl2_19 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    spl2_18 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl2_18),
% 0.21/0.52    inference(superposition,[],[f55,f346])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f345])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    spl2_18 | ~spl2_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f333,f322,f345])).
% 0.21/0.52  fof(f322,plain,(
% 0.21/0.52    spl2_16 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_16),
% 0.21/0.52    inference(superposition,[],[f111,f323])).
% 0.21/0.52  fof(f323,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(sK1,sK0) | ~spl2_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f322])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1) )),
% 0.21/0.52    inference(superposition,[],[f61,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f325,plain,(
% 0.21/0.52    spl2_16 | ~spl2_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f316,f311,f322])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    spl2_15 <=> sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(sK1,sK0) | ~spl2_15),
% 0.21/0.52    inference(superposition,[],[f50,f312])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl2_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f311])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    spl2_15 | ~spl2_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f309,f292,f311])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    spl2_13 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~spl2_13),
% 0.21/0.52    inference(forward_demodulation,[],[f308,f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.21/0.52    inference(superposition,[],[f127,f46])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f121,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    inference(rectify,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,X0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f50,f115])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k1_xboole_0,sK1) | ~spl2_13),
% 0.21/0.52    inference(forward_demodulation,[],[f302,f46])).
% 0.21/0.52  fof(f302,plain,(
% 0.21/0.52    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) | ~spl2_13),
% 0.21/0.52    inference(superposition,[],[f50,f293])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | ~spl2_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f292])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    spl2_13 | ~spl2_1 | ~spl2_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f290,f276,f65,f292])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    spl2_1 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    spl2_11 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) | (~spl2_1 | ~spl2_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f289,f277])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f276])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    k1_xboole_0 = k4_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl2_1),
% 0.21/0.52    inference(resolution,[],[f71,f57])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    spl2_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f287])).
% 0.21/0.52  fof(f287,plain,(
% 0.21/0.52    $false | spl2_8),
% 0.21/0.52    inference(resolution,[],[f260,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,sK0) | spl2_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f259])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl2_8 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ~spl2_4 | spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f279,f68,f82])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    spl2_2 <=> sK1 = k2_subset_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    sK0 != sK1 | spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f69,f41])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    sK1 != k2_subset_1(sK0) | spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    spl2_11 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f248,f75,f276])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_3),
% 0.21/0.52    inference(resolution,[],[f52,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl2_10 | ~spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f262,f75,f272])).
% 0.21/0.52  fof(f272,plain,(
% 0.21/0.52    spl2_10 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_3),
% 0.21/0.52    inference(resolution,[],[f53,f76])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    ~spl2_8 | spl2_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f257,f91,f259])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl2_6 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,sK0) | spl2_6),
% 0.21/0.52    inference(superposition,[],[f92,f256])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl2_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ~spl2_6 | spl2_1 | ~spl2_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f89,f82,f65,f91])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | (spl2_1 | ~spl2_4)),
% 0.21/0.52    inference(superposition,[],[f66,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl2_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ~r1_tarski(k3_subset_1(sK0,sK1),sK1) | spl2_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f65])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl2_4 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f80,f68,f82])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    sK0 = sK1 | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f72,f41])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    sK1 = k2_subset_1(sK0) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f68])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl2_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f37,f75])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f33,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f20])).
% 0.21/0.52  fof(f20,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl2_1 | spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f68,f65])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ~spl2_1 | ~spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f39,f68,f65])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (15026)------------------------------
% 0.21/0.52  % (15026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15026)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (15026)Memory used [KB]: 10874
% 0.21/0.52  % (15026)Time elapsed: 0.135 s
% 0.21/0.52  % (15026)------------------------------
% 0.21/0.52  % (15026)------------------------------
% 0.21/0.52  % (15012)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (15019)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15028)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (15029)Refutation not found, incomplete strategy% (15029)------------------------------
% 0.21/0.52  % (15029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15029)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (15029)Memory used [KB]: 10746
% 0.21/0.52  % (15029)Time elapsed: 0.063 s
% 0.21/0.52  % (15029)------------------------------
% 0.21/0.52  % (15029)------------------------------
% 0.21/0.52  % (15022)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (15022)Refutation not found, incomplete strategy% (15022)------------------------------
% 0.21/0.53  % (15022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (15022)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15022)Memory used [KB]: 6140
% 0.21/0.53  % (15022)Time elapsed: 0.002 s
% 0.21/0.53  % (15022)------------------------------
% 0.21/0.53  % (15022)------------------------------
% 0.21/0.53  % (15007)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (15018)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (15023)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (15025)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (15020)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (15010)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (15024)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (15024)Refutation not found, incomplete strategy% (15024)------------------------------
% 0.21/0.54  % (15024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (15024)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (15024)Memory used [KB]: 10618
% 0.21/0.54  % (15024)Time elapsed: 0.130 s
% 0.21/0.54  % (15024)------------------------------
% 0.21/0.54  % (15024)------------------------------
% 0.21/0.54  % (15030)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (15027)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (15033)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (15032)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (15031)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (15014)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (15013)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (15000)Success in time 0.185 s
%------------------------------------------------------------------------------
