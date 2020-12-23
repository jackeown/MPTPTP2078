%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 246 expanded)
%              Number of leaves         :   32 ( 100 expanded)
%              Depth                    :   11
%              Number of atoms          :  205 ( 388 expanded)
%              Number of equality atoms :   90 ( 206 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f301,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f69,f76,f85,f99,f115,f130,f162,f235,f257,f275,f298,f299])).

fof(f299,plain,
    ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | sK0 != k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f298,plain,
    ( spl2_24
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f293,f272,f295])).

fof(f295,plain,
    ( spl2_24
  <=> sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f272,plain,
    ( spl2_21
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f293,plain,
    ( sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f285,f48])).

fof(f48,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f31,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f285,plain,
    ( k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0))
    | ~ spl2_21 ),
    inference(superposition,[],[f50,f274])).

fof(f274,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f272])).

fof(f50,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f46,f46])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f275,plain,
    ( spl2_21
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f267,f254,f272])).

fof(f254,plain,
    ( spl2_20
  <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f267,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_20 ),
    inference(superposition,[],[f219,f256])).

fof(f256,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f254])).

fof(f219,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f218,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f47,f32])).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f218,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f212,f32])).

fof(f212,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0)) ),
    inference(superposition,[],[f205,f70])).

fof(f205,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(forward_demodulation,[],[f52,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f43,f46,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f257,plain,
    ( spl2_20
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f252,f159,f95,f81,f254])).

fof(f81,plain,
    ( spl2_5
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f95,plain,
    ( spl2_7
  <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f159,plain,
    ( spl2_15
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f252,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f251,f161])).

fof(f161,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f159])).

fof(f251,plain,
    ( k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f97,f83])).

fof(f83,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f97,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f235,plain,
    ( spl2_17
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f234,f121,f60,f189])).

fof(f189,plain,
    ( spl2_17
  <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f60,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f121,plain,
    ( spl2_10
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f234,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f233,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f33,f46,f46])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f233,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f229,f50])).

fof(f229,plain,
    ( k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f178,f123])).

fof(f123,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0)) )
    | ~ spl2_2 ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f162,plain,
    ( spl2_15
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f157,f111,f81,f159])).

fof(f111,plain,
    ( spl2_9
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f157,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_5
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f113,f83])).

fof(f113,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f130,plain,
    ( ~ spl2_2
    | spl2_10
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f119,f81,f121,f60])).

fof(f119,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_5 ),
    inference(superposition,[],[f38,f83])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f115,plain,
    ( spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f102,f60,f111])).

fof(f102,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f40,f62])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f99,plain,
    ( spl2_7
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f88,f73,f95])).

fof(f73,plain,
    ( spl2_4
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f88,plain,
    ( k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl2_4 ),
    inference(resolution,[],[f75,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f75,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f85,plain,
    ( spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f78,f60,f81])).

fof(f78,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f39,f62])).

fof(f76,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f60,f73])).

fof(f71,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f62,f38])).

fof(f69,plain,
    ( ~ spl2_3
    | spl2_1 ),
    inference(avatar_split_clause,[],[f64,f55,f66])).

fof(f66,plain,
    ( spl2_3
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f55,plain,
    ( spl2_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f64,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_1 ),
    inference(backward_demodulation,[],[f57,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f63,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f27,f60])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f58,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:25:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (20193)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.43  % (20192)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.43  % (20196)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.43  % (20195)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.43  % (20188)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.43  % (20187)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.43  % (20191)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.43  % (20199)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.44  % (20200)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.44  % (20191)Refutation found. Thanks to Tanya!
% 0.19/0.44  % SZS status Theorem for theBenchmark
% 0.19/0.44  % (20190)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.44  % (20194)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.44  % (20202)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.44  % (20198)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.44  % (20201)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.45  % (20186)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.45  % (20189)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f301,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(avatar_sat_refutation,[],[f58,f63,f69,f76,f85,f99,f115,f130,f162,f235,f257,f275,f298,f299])).
% 0.19/0.45  fof(f299,plain,(
% 0.19/0.45    k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) | sK0 != k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) != k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.45    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.45  fof(f298,plain,(
% 0.19/0.45    spl2_24 | ~spl2_21),
% 0.19/0.45    inference(avatar_split_clause,[],[f293,f272,f295])).
% 0.19/0.45  fof(f295,plain,(
% 0.19/0.45    spl2_24 <=> sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.19/0.45  fof(f272,plain,(
% 0.19/0.45    spl2_21 <=> k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.19/0.45  fof(f293,plain,(
% 0.19/0.45    sK0 = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | ~spl2_21),
% 0.19/0.45    inference(forward_demodulation,[],[f285,f48])).
% 0.19/0.45  fof(f48,plain,(
% 0.19/0.45    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.19/0.45    inference(definition_unfolding,[],[f31,f46])).
% 0.19/0.45  fof(f46,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f34,f45])).
% 0.19/0.45  fof(f45,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f35,f41])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,axiom,(
% 0.19/0.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.45  fof(f34,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.45  fof(f31,plain,(
% 0.19/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.45  fof(f285,plain,(
% 0.19/0.45    k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,k1_xboole_0)) | ~spl2_21),
% 0.19/0.45    inference(superposition,[],[f50,f274])).
% 0.19/0.45  fof(f274,plain,(
% 0.19/0.45    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_21),
% 0.19/0.45    inference(avatar_component_clause,[],[f272])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X0,X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f36,f46,f46])).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f4])).
% 0.19/0.45  fof(f4,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.19/0.45  fof(f275,plain,(
% 0.19/0.45    spl2_21 | ~spl2_20),
% 0.19/0.45    inference(avatar_split_clause,[],[f267,f254,f272])).
% 0.19/0.45  fof(f254,plain,(
% 0.19/0.45    spl2_20 <=> sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.19/0.45  fof(f267,plain,(
% 0.19/0.45    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_20),
% 0.19/0.45    inference(superposition,[],[f219,f256])).
% 0.19/0.45  fof(f256,plain,(
% 0.19/0.45    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_20),
% 0.19/0.45    inference(avatar_component_clause,[],[f254])).
% 0.19/0.45  fof(f219,plain,(
% 0.19/0.45    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 0.19/0.45    inference(forward_demodulation,[],[f218,f70])).
% 0.19/0.45  fof(f70,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.19/0.45    inference(forward_demodulation,[],[f47,f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.45  fof(f47,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f30,f37])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f3])).
% 0.19/0.45  fof(f3,axiom,(
% 0.19/0.45    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.19/0.45  fof(f218,plain,(
% 0.19/0.45    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 0.19/0.45    inference(forward_demodulation,[],[f212,f32])).
% 0.19/0.45  fof(f212,plain,(
% 0.19/0.45    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),k1_xboole_0))) )),
% 0.19/0.45    inference(superposition,[],[f205,f70])).
% 0.19/0.45  fof(f205,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.19/0.45    inference(forward_demodulation,[],[f52,f51])).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f42,f46])).
% 0.19/0.45  fof(f42,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.19/0.45  fof(f52,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f43,f46,f37])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.19/0.45  fof(f257,plain,(
% 0.19/0.45    spl2_20 | ~spl2_5 | ~spl2_7 | ~spl2_15),
% 0.19/0.45    inference(avatar_split_clause,[],[f252,f159,f95,f81,f254])).
% 0.19/0.45  fof(f81,plain,(
% 0.19/0.45    spl2_5 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.45  fof(f95,plain,(
% 0.19/0.45    spl2_7 <=> k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.45  fof(f159,plain,(
% 0.19/0.45    spl2_15 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.19/0.45  fof(f252,plain,(
% 0.19/0.45    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_5 | ~spl2_7 | ~spl2_15)),
% 0.19/0.45    inference(forward_demodulation,[],[f251,f161])).
% 0.19/0.45  fof(f161,plain,(
% 0.19/0.45    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_15),
% 0.19/0.45    inference(avatar_component_clause,[],[f159])).
% 0.19/0.45  fof(f251,plain,(
% 0.19/0.45    k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_5 | ~spl2_7)),
% 0.19/0.45    inference(forward_demodulation,[],[f97,f83])).
% 0.19/0.45  fof(f83,plain,(
% 0.19/0.45    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_5),
% 0.19/0.45    inference(avatar_component_clause,[],[f81])).
% 0.19/0.45  fof(f97,plain,(
% 0.19/0.45    k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_7),
% 0.19/0.45    inference(avatar_component_clause,[],[f95])).
% 0.19/0.45  fof(f235,plain,(
% 0.19/0.45    spl2_17 | ~spl2_2 | ~spl2_10),
% 0.19/0.45    inference(avatar_split_clause,[],[f234,f121,f60,f189])).
% 0.19/0.45  fof(f189,plain,(
% 0.19/0.45    spl2_17 <=> k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.19/0.45  fof(f60,plain,(
% 0.19/0.45    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.45  fof(f121,plain,(
% 0.19/0.45    spl2_10 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.45  fof(f234,plain,(
% 0.19/0.45    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK0,sK0,sK0,sK1)) | (~spl2_2 | ~spl2_10)),
% 0.19/0.45    inference(forward_demodulation,[],[f233,f49])).
% 0.19/0.45  fof(f49,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f33,f46,f46])).
% 0.19/0.45  fof(f33,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f1])).
% 0.19/0.45  fof(f1,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.45  fof(f233,plain,(
% 0.19/0.45    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK0)) | (~spl2_2 | ~spl2_10)),
% 0.19/0.45    inference(forward_demodulation,[],[f229,f50])).
% 0.19/0.45  fof(f229,plain,(
% 0.19/0.45    k4_subset_1(sK0,sK1,k4_xboole_0(sK0,sK1)) = k3_tarski(k2_enumset1(sK1,sK1,sK1,k4_xboole_0(sK0,sK1))) | (~spl2_2 | ~spl2_10)),
% 0.19/0.45    inference(resolution,[],[f178,f123])).
% 0.19/0.45  fof(f123,plain,(
% 0.19/0.45    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_10),
% 0.19/0.45    inference(avatar_component_clause,[],[f121])).
% 0.19/0.45  fof(f178,plain,(
% 0.19/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,X0))) ) | ~spl2_2),
% 0.19/0.45    inference(resolution,[],[f53,f62])).
% 0.19/0.45  fof(f62,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.19/0.45    inference(avatar_component_clause,[],[f60])).
% 0.19/0.45  fof(f53,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k2_enumset1(X1,X1,X1,X2))) )),
% 0.19/0.45    inference(definition_unfolding,[],[f44,f46])).
% 0.19/0.45  fof(f44,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f24])).
% 0.19/0.45  fof(f24,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(flattening,[],[f23])).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.19/0.45    inference(ennf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.19/0.45  fof(f162,plain,(
% 0.19/0.45    spl2_15 | ~spl2_5 | ~spl2_9),
% 0.19/0.45    inference(avatar_split_clause,[],[f157,f111,f81,f159])).
% 0.19/0.45  fof(f111,plain,(
% 0.19/0.45    spl2_9 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.45  fof(f157,plain,(
% 0.19/0.45    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl2_5 | ~spl2_9)),
% 0.19/0.45    inference(forward_demodulation,[],[f113,f83])).
% 0.19/0.45  fof(f113,plain,(
% 0.19/0.45    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_9),
% 0.19/0.45    inference(avatar_component_clause,[],[f111])).
% 0.19/0.45  fof(f130,plain,(
% 0.19/0.45    ~spl2_2 | spl2_10 | ~spl2_5),
% 0.19/0.45    inference(avatar_split_clause,[],[f119,f81,f121,f60])).
% 0.19/0.45  fof(f119,plain,(
% 0.19/0.45    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_5),
% 0.19/0.45    inference(superposition,[],[f38,f83])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f20])).
% 0.19/0.45  fof(f20,plain,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.19/0.45  fof(f115,plain,(
% 0.19/0.45    spl2_9 | ~spl2_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f102,f60,f111])).
% 0.19/0.45  fof(f102,plain,(
% 0.19/0.45    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_2),
% 0.19/0.45    inference(resolution,[],[f40,f62])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.19/0.45    inference(cnf_transformation,[],[f22])).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.19/0.45  fof(f99,plain,(
% 0.19/0.45    spl2_7 | ~spl2_4),
% 0.19/0.45    inference(avatar_split_clause,[],[f88,f73,f95])).
% 0.19/0.45  fof(f73,plain,(
% 0.19/0.45    spl2_4 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.45  fof(f88,plain,(
% 0.19/0.45    k4_xboole_0(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl2_4),
% 0.19/0.45    inference(resolution,[],[f75,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f21])).
% 0.19/0.45  fof(f21,plain,(
% 0.19/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f13])).
% 0.19/0.45  fof(f13,axiom,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.45  fof(f75,plain,(
% 0.19/0.45    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_4),
% 0.19/0.45    inference(avatar_component_clause,[],[f73])).
% 0.19/0.45  fof(f85,plain,(
% 0.19/0.45    spl2_5 | ~spl2_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f78,f60,f81])).
% 0.19/0.45  fof(f78,plain,(
% 0.19/0.45    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl2_2),
% 0.19/0.45    inference(resolution,[],[f39,f62])).
% 0.19/0.45  fof(f76,plain,(
% 0.19/0.45    spl2_4 | ~spl2_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f71,f60,f73])).
% 0.19/0.45  fof(f71,plain,(
% 0.19/0.45    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f62,f38])).
% 0.19/0.45  fof(f69,plain,(
% 0.19/0.45    ~spl2_3 | spl2_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f64,f55,f66])).
% 0.19/0.45  fof(f66,plain,(
% 0.19/0.45    spl2_3 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    spl2_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.45  fof(f64,plain,(
% 0.19/0.45    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_1),
% 0.19/0.45    inference(backward_demodulation,[],[f57,f29])).
% 0.19/0.45  fof(f29,plain,(
% 0.19/0.45    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.19/0.45    inference(cnf_transformation,[],[f12])).
% 0.19/0.45  fof(f12,axiom,(
% 0.19/0.45    ! [X0] : k2_subset_1(X0) = X0),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.19/0.45  fof(f57,plain,(
% 0.19/0.45    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl2_1),
% 0.19/0.45    inference(avatar_component_clause,[],[f55])).
% 0.19/0.45  fof(f63,plain,(
% 0.19/0.45    spl2_2),
% 0.19/0.45    inference(avatar_split_clause,[],[f27,f60])).
% 0.19/0.45  fof(f27,plain,(
% 0.19/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  fof(f26,plain,(
% 0.19/0.45    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.45    introduced(choice_axiom,[])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.19/0.45    inference(negated_conjecture,[],[f17])).
% 0.19/0.45  fof(f17,conjecture,(
% 0.19/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 0.19/0.45  fof(f58,plain,(
% 0.19/0.45    ~spl2_1),
% 0.19/0.45    inference(avatar_split_clause,[],[f28,f55])).
% 0.19/0.45  fof(f28,plain,(
% 0.19/0.45    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.45    inference(cnf_transformation,[],[f26])).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (20191)------------------------------
% 0.19/0.45  % (20191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (20191)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (20191)Memory used [KB]: 6268
% 0.19/0.45  % (20191)Time elapsed: 0.049 s
% 0.19/0.45  % (20191)------------------------------
% 0.19/0.45  % (20191)------------------------------
% 0.19/0.45  % (20184)Success in time 0.109 s
%------------------------------------------------------------------------------
