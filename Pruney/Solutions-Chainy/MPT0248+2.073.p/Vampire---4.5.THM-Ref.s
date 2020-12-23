%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:00 EST 2020

% Result     : Theorem 2.29s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 685 expanded)
%              Number of leaves         :   47 ( 257 expanded)
%              Depth                    :   16
%              Number of atoms          :  424 (1060 expanded)
%              Number of equality atoms :  151 ( 673 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f956,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f129,f134,f150,f157,f158,f203,f227,f301,f319,f367,f378,f401,f513,f520,f545,f547,f553,f765,f796,f876,f910,f955])).

fof(f955,plain,
    ( spl5_9
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f945])).

fof(f945,plain,
    ( $false
    | spl5_9
    | ~ spl5_17 ),
    inference(unit_resulting_resolution,[],[f318,f202,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f202,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl5_9
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f318,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl5_17
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f910,plain,
    ( spl5_3
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f877,f873,f122])).

fof(f122,plain,
    ( spl5_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f873,plain,
    ( spl5_42
  <=> k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f877,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_42 ),
    inference(superposition,[],[f875,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f875,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f873])).

fof(f876,plain,
    ( spl5_42
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f856,f793,f873])).

fof(f793,plain,
    ( spl5_39
  <=> sK0 = k5_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f856,plain,
    ( k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl5_39 ),
    inference(superposition,[],[f803,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f803,plain,
    ( ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(sK2,k5_xboole_0(sK0,X0))
    | ~ spl5_39 ),
    inference(superposition,[],[f72,f795])).

fof(f795,plain,
    ( sK0 = k5_xboole_0(sK2,sK0)
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f793])).

fof(f72,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f796,plain,
    ( spl5_39
    | ~ spl5_20
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f784,f762,f375,f793])).

fof(f375,plain,
    ( spl5_20
  <=> sK0 = k5_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f762,plain,
    ( spl5_38
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f784,plain,
    ( sK0 = k5_xboole_0(sK2,sK0)
    | ~ spl5_20
    | ~ spl5_38 ),
    inference(forward_demodulation,[],[f775,f377])).

fof(f377,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f375])).

fof(f775,plain,
    ( k5_xboole_0(k1_xboole_0,sK0) = k5_xboole_0(sK2,sK0)
    | ~ spl5_20
    | ~ spl5_38 ),
    inference(superposition,[],[f766,f455])).

fof(f455,plain,
    ( ! [X0] : k5_xboole_0(X0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK0))
    | ~ spl5_20 ),
    inference(superposition,[],[f380,f50])).

fof(f50,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f380,plain,
    ( ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))
    | ~ spl5_20 ),
    inference(superposition,[],[f72,f377])).

fof(f766,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0))
    | ~ spl5_38 ),
    inference(superposition,[],[f72,f764])).

fof(f764,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f762])).

fof(f765,plain,
    ( spl5_38
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f752,f504,f762])).

fof(f504,plain,
    ( spl5_30
  <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f752,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f751,f44])).

fof(f751,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,sK1)
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f742,f45])).

fof(f742,plain,
    ( k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0))
    | ~ spl5_30 ),
    inference(superposition,[],[f598,f44])).

fof(f598,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))
    | ~ spl5_30 ),
    inference(forward_demodulation,[],[f593,f72])).

fof(f593,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),X0))
    | ~ spl5_30 ),
    inference(superposition,[],[f72,f505])).

fof(f505,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f504])).

fof(f553,plain,
    ( ~ spl5_15
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f550,f126,f280])).

fof(f280,plain,
    ( spl5_15
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f126,plain,
    ( spl5_4
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f550,plain,
    ( sK1 != sK2
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f549,f127])).

fof(f127,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f549,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f548])).

fof(f548,plain,
    ( sK1 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f90,f127])).

fof(f90,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f42,f87,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f71,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f74,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f76,f77])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f547,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f545,plain,
    ( ~ spl5_4
    | spl5_7
    | ~ spl5_32 ),
    inference(avatar_contradiction_clause,[],[f541])).

fof(f541,plain,
    ( $false
    | ~ spl5_4
    | spl5_7
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f156,f519,f348])).

fof(f348,plain,
    ( ! [X13] :
        ( ~ r2_hidden(sK0,X13)
        | r1_tarski(sK1,X13) )
    | ~ spl5_4 ),
    inference(superposition,[],[f106,f127])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f69,f87])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f519,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl5_32
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f156,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl5_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f520,plain,
    ( spl5_32
    | ~ spl5_4
    | spl5_29 ),
    inference(avatar_split_clause,[],[f515,f500,f126,f517])).

fof(f500,plain,
    ( spl5_29
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f515,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl5_4
    | spl5_29 ),
    inference(resolution,[],[f501,f345])).

fof(f345,plain,
    ( ! [X10] :
        ( r1_xboole_0(sK1,X10)
        | r2_hidden(sK0,X10) )
    | ~ spl5_4 ),
    inference(superposition,[],[f98,f127])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f87])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f501,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | spl5_29 ),
    inference(avatar_component_clause,[],[f500])).

fof(f513,plain,
    ( ~ spl5_29
    | spl5_30
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f432,f398,f504,f500])).

fof(f398,plain,
    ( spl5_23
  <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f432,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f426,f50])).

fof(f426,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_23 ),
    inference(superposition,[],[f100,f400])).

fof(f400,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f398])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f86])).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f53,f85])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f51,f84])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f401,plain,
    ( spl5_23
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f379,f131,f126,f398])).

fof(f131,plain,
    ( spl5_5
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f379,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f133,f127])).

fof(f133,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f378,plain,
    ( spl5_20
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f373,f323,f126,f375])).

fof(f323,plain,
    ( spl5_18
  <=> sK0 = k3_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f373,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,sK0)
    | ~ spl5_4
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f365,f325])).

fof(f325,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f323])).

fof(f365,plain,
    ( sK0 = k5_xboole_0(k1_xboole_0,k3_tarski(sK1))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f343,f44])).

fof(f343,plain,
    ( sK0 = k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f93,f127])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f47,f86])).

fof(f47,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f367,plain,
    ( spl5_18
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f344,f126,f323])).

fof(f344,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl5_4 ),
    inference(superposition,[],[f94,f127])).

fof(f94,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f85])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f319,plain,
    ( spl5_17
    | ~ spl5_12
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f315,f219,f131,f117,f223,f317])).

fof(f223,plain,
    ( spl5_12
  <=> r1_xboole_0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f117,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f219,plain,
    ( spl5_11
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,sK2)
        | ~ r2_hidden(X0,k1_xboole_0) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f314,f118])).

fof(f118,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r1_xboole_0(sK1,sK2) )
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f313,f220])).

fof(f220,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f219])).

fof(f313,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
        | ~ r1_xboole_0(sK1,sK2) )
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f144,f118])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
        | ~ r1_xboole_0(sK1,sK2) )
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f139,f72])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
        | ~ r1_xboole_0(sK1,sK2) )
    | ~ spl5_5 ),
    inference(superposition,[],[f97,f133])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f301,plain,
    ( spl5_9
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl5_9
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f202,f297,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f297,plain,
    ( ! [X0] : r2_hidden(X0,sK2)
    | spl5_12 ),
    inference(resolution,[],[f229,f111])).

fof(f111,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f67,f87])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
        | r2_hidden(X0,sK2) )
    | spl5_12 ),
    inference(resolution,[],[f228,f98])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK2)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | spl5_12 ),
    inference(resolution,[],[f224,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f224,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f223])).

fof(f227,plain,
    ( spl5_11
    | ~ spl5_12
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f214,f131,f117,f223,f219])).

fof(f214,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK2)
    | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f213,f118])).

fof(f213,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f143,f118])).

fof(f143,plain,
    ( k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f137,f72])).

fof(f137,plain,
    ( k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(superposition,[],[f100,f133])).

fof(f203,plain,
    ( ~ spl5_9
    | ~ spl5_2
    | spl5_7 ),
    inference(avatar_split_clause,[],[f198,f154,f117,f200])).

fof(f198,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_2
    | spl5_7 ),
    inference(backward_demodulation,[],[f156,f118])).

fof(f158,plain,
    ( spl5_2
    | spl5_4
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f151,f147,f126,f117])).

fof(f147,plain,
    ( spl5_6
  <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f151,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1
    | ~ spl5_6 ),
    inference(resolution,[],[f149,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f66,f87,f87])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f149,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f157,plain,
    ( ~ spl5_7
    | spl5_1
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f135,f131,f113,f154])).

fof(f113,plain,
    ( spl5_1
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f135,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(superposition,[],[f133,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f85])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f150,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f141,f131,f147])).

fof(f141,plain,
    ( r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ spl5_5 ),
    inference(superposition,[],[f95,f133])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f49,f85])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f134,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f89,f131])).

fof(f89,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f43,f87,f85])).

fof(f43,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f92,f126,f122])).

fof(f92,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f40,f87])).

fof(f40,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f33])).

fof(f120,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f91,f117,f113])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f41,f87])).

fof(f41,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:49:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (21862)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (21886)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (21870)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (21868)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.57  % (21863)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.57  % (21860)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.48/0.57  % (21857)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.63/0.58  % (21858)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.63/0.58  % (21868)Refutation not found, incomplete strategy% (21868)------------------------------
% 1.63/0.58  % (21868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (21868)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (21868)Memory used [KB]: 10618
% 1.63/0.58  % (21868)Time elapsed: 0.152 s
% 1.63/0.58  % (21868)------------------------------
% 1.63/0.58  % (21868)------------------------------
% 1.63/0.58  % (21876)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.63/0.58  % (21859)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.63/0.58  % (21880)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.63/0.59  % (21885)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.63/0.59  % (21861)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.63/0.59  % (21878)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.63/0.59  % (21864)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.63/0.60  % (21866)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.63/0.60  % (21882)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.63/0.60  % (21875)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.63/0.60  % (21877)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.63/0.60  % (21881)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.63/0.60  % (21872)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.63/0.61  % (21883)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.63/0.61  % (21874)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.63/0.61  % (21884)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.63/0.61  % (21874)Refutation not found, incomplete strategy% (21874)------------------------------
% 1.63/0.61  % (21874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.61  % (21874)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.61  
% 1.63/0.61  % (21874)Memory used [KB]: 10618
% 1.63/0.61  % (21874)Time elapsed: 0.180 s
% 1.63/0.61  % (21874)------------------------------
% 1.63/0.61  % (21874)------------------------------
% 1.63/0.61  % (21873)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.63/0.61  % (21871)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.63/0.61  % (21869)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.62  % (21865)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.63/0.62  % (21867)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.63/0.62  % (21867)Refutation not found, incomplete strategy% (21867)------------------------------
% 1.63/0.62  % (21867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.62  % (21867)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.62  
% 1.63/0.62  % (21867)Memory used [KB]: 10618
% 1.63/0.62  % (21867)Time elapsed: 0.202 s
% 1.63/0.62  % (21867)------------------------------
% 1.63/0.62  % (21867)------------------------------
% 1.63/0.63  % (21879)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.29/0.70  % (21879)Refutation found. Thanks to Tanya!
% 2.29/0.70  % SZS status Theorem for theBenchmark
% 2.29/0.70  % SZS output start Proof for theBenchmark
% 2.29/0.70  fof(f956,plain,(
% 2.29/0.70    $false),
% 2.29/0.70    inference(avatar_sat_refutation,[],[f120,f129,f134,f150,f157,f158,f203,f227,f301,f319,f367,f378,f401,f513,f520,f545,f547,f553,f765,f796,f876,f910,f955])).
% 2.29/0.70  fof(f955,plain,(
% 2.29/0.70    spl5_9 | ~spl5_17),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f945])).
% 2.29/0.70  fof(f945,plain,(
% 2.29/0.70    $false | (spl5_9 | ~spl5_17)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f318,f202,f62])).
% 2.29/0.70  fof(f62,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f37])).
% 2.29/0.70  fof(f37,plain,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.29/0.70    inference(ennf_transformation,[],[f2])).
% 2.29/0.70  fof(f2,axiom,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.29/0.70  fof(f202,plain,(
% 2.29/0.70    ~r1_tarski(k1_xboole_0,sK2) | spl5_9),
% 2.29/0.70    inference(avatar_component_clause,[],[f200])).
% 2.29/0.70  fof(f200,plain,(
% 2.29/0.70    spl5_9 <=> r1_tarski(k1_xboole_0,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.29/0.70  fof(f318,plain,(
% 2.29/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl5_17),
% 2.29/0.70    inference(avatar_component_clause,[],[f317])).
% 2.29/0.70  fof(f317,plain,(
% 2.29/0.70    spl5_17 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.29/0.70  fof(f910,plain,(
% 2.29/0.70    spl5_3 | ~spl5_42),
% 2.29/0.70    inference(avatar_split_clause,[],[f877,f873,f122])).
% 2.29/0.70  fof(f122,plain,(
% 2.29/0.70    spl5_3 <=> k1_xboole_0 = sK2),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.29/0.70  fof(f873,plain,(
% 2.29/0.70    spl5_42 <=> k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 2.29/0.70  fof(f877,plain,(
% 2.29/0.70    k1_xboole_0 = sK2 | ~spl5_42),
% 2.29/0.70    inference(superposition,[],[f875,f45])).
% 2.29/0.70  fof(f45,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.29/0.70    inference(cnf_transformation,[],[f9])).
% 2.29/0.70  fof(f9,axiom,(
% 2.29/0.70    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.29/0.70  fof(f875,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) | ~spl5_42),
% 2.29/0.70    inference(avatar_component_clause,[],[f873])).
% 2.29/0.70  fof(f876,plain,(
% 2.29/0.70    spl5_42 | ~spl5_39),
% 2.29/0.70    inference(avatar_split_clause,[],[f856,f793,f873])).
% 2.29/0.70  fof(f793,plain,(
% 2.29/0.70    spl5_39 <=> sK0 = k5_xboole_0(sK2,sK0)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.29/0.70  fof(f856,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(sK2,k1_xboole_0) | ~spl5_39),
% 2.29/0.70    inference(superposition,[],[f803,f44])).
% 2.29/0.70  fof(f44,plain,(
% 2.29/0.70    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f13])).
% 2.29/0.70  fof(f13,axiom,(
% 2.29/0.70    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.29/0.70  fof(f803,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(sK2,k5_xboole_0(sK0,X0))) ) | ~spl5_39),
% 2.29/0.70    inference(superposition,[],[f72,f795])).
% 2.29/0.70  fof(f795,plain,(
% 2.29/0.70    sK0 = k5_xboole_0(sK2,sK0) | ~spl5_39),
% 2.29/0.70    inference(avatar_component_clause,[],[f793])).
% 2.29/0.70  fof(f72,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f12])).
% 2.29/0.70  fof(f12,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.29/0.70  fof(f796,plain,(
% 2.29/0.70    spl5_39 | ~spl5_20 | ~spl5_38),
% 2.29/0.70    inference(avatar_split_clause,[],[f784,f762,f375,f793])).
% 2.29/0.70  fof(f375,plain,(
% 2.29/0.70    spl5_20 <=> sK0 = k5_xboole_0(k1_xboole_0,sK0)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.29/0.70  fof(f762,plain,(
% 2.29/0.70    spl5_38 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.29/0.70  fof(f784,plain,(
% 2.29/0.70    sK0 = k5_xboole_0(sK2,sK0) | (~spl5_20 | ~spl5_38)),
% 2.29/0.70    inference(forward_demodulation,[],[f775,f377])).
% 2.29/0.70  fof(f377,plain,(
% 2.29/0.70    sK0 = k5_xboole_0(k1_xboole_0,sK0) | ~spl5_20),
% 2.29/0.70    inference(avatar_component_clause,[],[f375])).
% 2.29/0.70  fof(f775,plain,(
% 2.29/0.70    k5_xboole_0(k1_xboole_0,sK0) = k5_xboole_0(sK2,sK0) | (~spl5_20 | ~spl5_38)),
% 2.29/0.70    inference(superposition,[],[f766,f455])).
% 2.29/0.70  fof(f455,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(X0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,sK0))) ) | ~spl5_20),
% 2.29/0.70    inference(superposition,[],[f380,f50])).
% 2.29/0.70  fof(f50,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f1])).
% 2.29/0.70  fof(f1,axiom,(
% 2.29/0.70    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.29/0.70  fof(f380,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK0,X0))) ) | ~spl5_20),
% 2.29/0.70    inference(superposition,[],[f72,f377])).
% 2.29/0.70  fof(f766,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,X0))) ) | ~spl5_38),
% 2.29/0.70    inference(superposition,[],[f72,f764])).
% 2.29/0.70  fof(f764,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) | ~spl5_38),
% 2.29/0.70    inference(avatar_component_clause,[],[f762])).
% 2.29/0.70  fof(f765,plain,(
% 2.29/0.70    spl5_38 | ~spl5_30),
% 2.29/0.70    inference(avatar_split_clause,[],[f752,f504,f762])).
% 2.29/0.70  fof(f504,plain,(
% 2.29/0.70    spl5_30 <=> k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.29/0.70  fof(f752,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,sK2) | ~spl5_30),
% 2.29/0.70    inference(forward_demodulation,[],[f751,f44])).
% 2.29/0.70  fof(f751,plain,(
% 2.29/0.70    k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,sK1) | ~spl5_30),
% 2.29/0.70    inference(forward_demodulation,[],[f742,f45])).
% 2.29/0.70  fof(f742,plain,(
% 2.29/0.70    k5_xboole_0(k1_xboole_0,sK2) = k5_xboole_0(sK1,k5_xboole_0(sK1,k1_xboole_0)) | ~spl5_30),
% 2.29/0.70    inference(superposition,[],[f598,f44])).
% 2.29/0.70  fof(f598,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK2,X0)))) ) | ~spl5_30),
% 2.29/0.70    inference(forward_demodulation,[],[f593,f72])).
% 2.29/0.70  fof(f593,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),X0))) ) | ~spl5_30),
% 2.29/0.70    inference(superposition,[],[f72,f505])).
% 2.29/0.70  fof(f505,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl5_30),
% 2.29/0.70    inference(avatar_component_clause,[],[f504])).
% 2.29/0.70  fof(f553,plain,(
% 2.29/0.70    ~spl5_15 | ~spl5_4),
% 2.29/0.70    inference(avatar_split_clause,[],[f550,f126,f280])).
% 2.29/0.70  fof(f280,plain,(
% 2.29/0.70    spl5_15 <=> sK1 = sK2),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.29/0.70  fof(f126,plain,(
% 2.29/0.70    spl5_4 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.29/0.70  fof(f550,plain,(
% 2.29/0.70    sK1 != sK2 | ~spl5_4),
% 2.29/0.70    inference(forward_demodulation,[],[f549,f127])).
% 2.29/0.70  fof(f127,plain,(
% 2.29/0.70    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_4),
% 2.29/0.70    inference(avatar_component_clause,[],[f126])).
% 2.29/0.70  fof(f549,plain,(
% 2.29/0.70    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_4),
% 2.29/0.70    inference(trivial_inequality_removal,[],[f548])).
% 2.29/0.70  fof(f548,plain,(
% 2.29/0.70    sK1 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl5_4),
% 2.29/0.70    inference(forward_demodulation,[],[f90,f127])).
% 2.29/0.70  fof(f90,plain,(
% 2.29/0.70    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.29/0.70    inference(definition_unfolding,[],[f42,f87,f87])).
% 2.29/0.70  fof(f87,plain,(
% 2.29/0.70    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f46,f84])).
% 2.29/0.70  fof(f84,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f52,f83])).
% 2.29/0.70  fof(f83,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f71,f82])).
% 2.29/0.70  fof(f82,plain,(
% 2.29/0.70    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f74,f81])).
% 2.29/0.70  fof(f81,plain,(
% 2.29/0.70    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f75,f80])).
% 2.29/0.70  fof(f80,plain,(
% 2.29/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f76,f77])).
% 2.29/0.70  fof(f77,plain,(
% 2.29/0.70    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f23])).
% 2.29/0.70  fof(f23,axiom,(
% 2.29/0.70    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.29/0.70  fof(f76,plain,(
% 2.29/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f22])).
% 2.29/0.70  fof(f22,axiom,(
% 2.29/0.70    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.29/0.70  fof(f75,plain,(
% 2.29/0.70    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f21])).
% 2.29/0.70  fof(f21,axiom,(
% 2.29/0.70    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.29/0.70  fof(f74,plain,(
% 2.29/0.70    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f20])).
% 2.29/0.70  fof(f20,axiom,(
% 2.29/0.70    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.29/0.70  fof(f71,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f19])).
% 2.29/0.70  fof(f19,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.29/0.70  fof(f52,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f18])).
% 2.29/0.70  fof(f18,axiom,(
% 2.29/0.70    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.29/0.70  fof(f46,plain,(
% 2.29/0.70    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f17])).
% 2.29/0.70  fof(f17,axiom,(
% 2.29/0.70    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.29/0.70  fof(f42,plain,(
% 2.29/0.70    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.29/0.70    inference(cnf_transformation,[],[f33])).
% 2.29/0.70  fof(f33,plain,(
% 2.29/0.70    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.29/0.70    inference(ennf_transformation,[],[f29])).
% 2.29/0.70  fof(f29,negated_conjecture,(
% 2.29/0.70    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.29/0.70    inference(negated_conjecture,[],[f28])).
% 2.29/0.70  fof(f28,conjecture,(
% 2.29/0.70    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.29/0.70  fof(f547,plain,(
% 2.29/0.70    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 = sK2),
% 2.29/0.70    introduced(theory_tautology_sat_conflict,[])).
% 2.29/0.70  fof(f545,plain,(
% 2.29/0.70    ~spl5_4 | spl5_7 | ~spl5_32),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f541])).
% 2.29/0.70  fof(f541,plain,(
% 2.29/0.70    $false | (~spl5_4 | spl5_7 | ~spl5_32)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f156,f519,f348])).
% 2.29/0.70  fof(f348,plain,(
% 2.29/0.70    ( ! [X13] : (~r2_hidden(sK0,X13) | r1_tarski(sK1,X13)) ) | ~spl5_4),
% 2.29/0.70    inference(superposition,[],[f106,f127])).
% 2.29/0.70  fof(f106,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f69,f87])).
% 2.29/0.70  fof(f69,plain,(
% 2.29/0.70    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f24])).
% 2.29/0.70  fof(f24,axiom,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.29/0.70  fof(f519,plain,(
% 2.29/0.70    r2_hidden(sK0,sK2) | ~spl5_32),
% 2.29/0.70    inference(avatar_component_clause,[],[f517])).
% 2.29/0.70  fof(f517,plain,(
% 2.29/0.70    spl5_32 <=> r2_hidden(sK0,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.29/0.70  fof(f156,plain,(
% 2.29/0.70    ~r1_tarski(sK1,sK2) | spl5_7),
% 2.29/0.70    inference(avatar_component_clause,[],[f154])).
% 2.29/0.70  fof(f154,plain,(
% 2.29/0.70    spl5_7 <=> r1_tarski(sK1,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.29/0.70  fof(f520,plain,(
% 2.29/0.70    spl5_32 | ~spl5_4 | spl5_29),
% 2.29/0.70    inference(avatar_split_clause,[],[f515,f500,f126,f517])).
% 2.29/0.70  fof(f500,plain,(
% 2.29/0.70    spl5_29 <=> r1_xboole_0(sK1,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.29/0.70  fof(f515,plain,(
% 2.29/0.70    r2_hidden(sK0,sK2) | (~spl5_4 | spl5_29)),
% 2.29/0.70    inference(resolution,[],[f501,f345])).
% 2.29/0.70  fof(f345,plain,(
% 2.29/0.70    ( ! [X10] : (r1_xboole_0(sK1,X10) | r2_hidden(sK0,X10)) ) | ~spl5_4),
% 2.29/0.70    inference(superposition,[],[f98,f127])).
% 2.29/0.70  fof(f98,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f56,f87])).
% 2.29/0.70  fof(f56,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f35])).
% 2.29/0.70  fof(f35,plain,(
% 2.29/0.70    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.29/0.70    inference(ennf_transformation,[],[f25])).
% 2.29/0.70  fof(f25,axiom,(
% 2.29/0.70    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.29/0.70  fof(f501,plain,(
% 2.29/0.70    ~r1_xboole_0(sK1,sK2) | spl5_29),
% 2.29/0.70    inference(avatar_component_clause,[],[f500])).
% 2.29/0.70  fof(f513,plain,(
% 2.29/0.70    ~spl5_29 | spl5_30 | ~spl5_23),
% 2.29/0.70    inference(avatar_split_clause,[],[f432,f398,f504,f500])).
% 2.29/0.70  fof(f398,plain,(
% 2.29/0.70    spl5_23 <=> sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.29/0.70  fof(f432,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~r1_xboole_0(sK1,sK2) | ~spl5_23),
% 2.29/0.70    inference(forward_demodulation,[],[f426,f50])).
% 2.29/0.70  fof(f426,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~r1_xboole_0(sK1,sK2) | ~spl5_23),
% 2.29/0.70    inference(superposition,[],[f100,f400])).
% 2.29/0.70  fof(f400,plain,(
% 2.29/0.70    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_23),
% 2.29/0.70    inference(avatar_component_clause,[],[f398])).
% 2.29/0.70  fof(f100,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f65,f86])).
% 2.29/0.70  fof(f86,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.29/0.70    inference(definition_unfolding,[],[f53,f85])).
% 2.29/0.70  fof(f85,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.29/0.70    inference(definition_unfolding,[],[f51,f84])).
% 2.29/0.70  fof(f51,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f27])).
% 2.29/0.70  fof(f27,axiom,(
% 2.29/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.29/0.70  fof(f53,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f14])).
% 2.29/0.70  fof(f14,axiom,(
% 2.29/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.29/0.70  fof(f65,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f3])).
% 2.29/0.70  fof(f3,axiom,(
% 2.29/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.29/0.70  fof(f401,plain,(
% 2.29/0.70    spl5_23 | ~spl5_4 | ~spl5_5),
% 2.29/0.70    inference(avatar_split_clause,[],[f379,f131,f126,f398])).
% 2.29/0.70  fof(f131,plain,(
% 2.29/0.70    spl5_5 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.29/0.70  fof(f379,plain,(
% 2.29/0.70    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (~spl5_4 | ~spl5_5)),
% 2.29/0.70    inference(forward_demodulation,[],[f133,f127])).
% 2.29/0.70  fof(f133,plain,(
% 2.29/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl5_5),
% 2.29/0.70    inference(avatar_component_clause,[],[f131])).
% 2.29/0.70  fof(f378,plain,(
% 2.29/0.70    spl5_20 | ~spl5_4 | ~spl5_18),
% 2.29/0.70    inference(avatar_split_clause,[],[f373,f323,f126,f375])).
% 2.29/0.70  fof(f323,plain,(
% 2.29/0.70    spl5_18 <=> sK0 = k3_tarski(sK1)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.29/0.70  fof(f373,plain,(
% 2.29/0.70    sK0 = k5_xboole_0(k1_xboole_0,sK0) | (~spl5_4 | ~spl5_18)),
% 2.29/0.70    inference(forward_demodulation,[],[f365,f325])).
% 2.29/0.70  fof(f325,plain,(
% 2.29/0.70    sK0 = k3_tarski(sK1) | ~spl5_18),
% 2.29/0.70    inference(avatar_component_clause,[],[f323])).
% 2.29/0.70  fof(f365,plain,(
% 2.29/0.70    sK0 = k5_xboole_0(k1_xboole_0,k3_tarski(sK1)) | ~spl5_4),
% 2.29/0.70    inference(forward_demodulation,[],[f343,f44])).
% 2.29/0.70  fof(f343,plain,(
% 2.29/0.70    sK0 = k5_xboole_0(k5_xboole_0(sK0,sK0),k3_tarski(sK1)) | ~spl5_4),
% 2.29/0.70    inference(superposition,[],[f93,f127])).
% 2.29/0.70  fof(f93,plain,(
% 2.29/0.70    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.29/0.70    inference(definition_unfolding,[],[f47,f86])).
% 2.29/0.70  fof(f47,plain,(
% 2.29/0.70    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.29/0.70    inference(cnf_transformation,[],[f30])).
% 2.29/0.70  fof(f30,plain,(
% 2.29/0.70    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.29/0.70    inference(rectify,[],[f5])).
% 2.29/0.70  fof(f5,axiom,(
% 2.29/0.70    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.29/0.70  fof(f367,plain,(
% 2.29/0.70    spl5_18 | ~spl5_4),
% 2.29/0.70    inference(avatar_split_clause,[],[f344,f126,f323])).
% 2.29/0.70  fof(f344,plain,(
% 2.29/0.70    sK0 = k3_tarski(sK1) | ~spl5_4),
% 2.29/0.70    inference(superposition,[],[f94,f127])).
% 2.29/0.70  fof(f94,plain,(
% 2.29/0.70    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.29/0.70    inference(definition_unfolding,[],[f48,f85])).
% 2.29/0.70  fof(f48,plain,(
% 2.29/0.70    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.29/0.70    inference(cnf_transformation,[],[f31])).
% 2.29/0.70  fof(f31,plain,(
% 2.29/0.70    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.29/0.70    inference(rectify,[],[f4])).
% 2.29/0.70  fof(f4,axiom,(
% 2.29/0.70    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.29/0.70  fof(f319,plain,(
% 2.29/0.70    spl5_17 | ~spl5_12 | ~spl5_2 | ~spl5_5 | ~spl5_11),
% 2.29/0.70    inference(avatar_split_clause,[],[f315,f219,f131,f117,f223,f317])).
% 2.29/0.70  fof(f223,plain,(
% 2.29/0.70    spl5_12 <=> r1_xboole_0(k1_xboole_0,sK2)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.29/0.70  fof(f117,plain,(
% 2.29/0.70    spl5_2 <=> k1_xboole_0 = sK1),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.29/0.70  fof(f219,plain,(
% 2.29/0.70    spl5_11 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.29/0.70  fof(f315,plain,(
% 2.29/0.70    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,sK2) | ~r2_hidden(X0,k1_xboole_0)) ) | (~spl5_2 | ~spl5_5 | ~spl5_11)),
% 2.29/0.70    inference(forward_demodulation,[],[f314,f118])).
% 2.29/0.70  fof(f118,plain,(
% 2.29/0.70    k1_xboole_0 = sK1 | ~spl5_2),
% 2.29/0.70    inference(avatar_component_clause,[],[f117])).
% 2.29/0.70  fof(f314,plain,(
% 2.29/0.70    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r1_xboole_0(sK1,sK2)) ) | (~spl5_2 | ~spl5_5 | ~spl5_11)),
% 2.29/0.70    inference(forward_demodulation,[],[f313,f220])).
% 2.29/0.70  fof(f220,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~spl5_11),
% 2.29/0.70    inference(avatar_component_clause,[],[f219])).
% 2.29/0.70  fof(f313,plain,(
% 2.29/0.70    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r1_xboole_0(sK1,sK2)) ) | (~spl5_2 | ~spl5_5)),
% 2.29/0.70    inference(forward_demodulation,[],[f144,f118])).
% 2.29/0.70  fof(f144,plain,(
% 2.29/0.70    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | ~r1_xboole_0(sK1,sK2)) ) | ~spl5_5),
% 2.29/0.70    inference(forward_demodulation,[],[f139,f72])).
% 2.29/0.70  fof(f139,plain,(
% 2.29/0.70    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,sK2)) ) | ~spl5_5),
% 2.29/0.70    inference(superposition,[],[f97,f133])).
% 2.29/0.70  fof(f97,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f54,f86])).
% 2.29/0.70  fof(f54,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f34])).
% 2.29/0.70  fof(f34,plain,(
% 2.29/0.70    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.29/0.70    inference(ennf_transformation,[],[f32])).
% 2.29/0.70  fof(f32,plain,(
% 2.29/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.29/0.70    inference(rectify,[],[f6])).
% 2.29/0.70  fof(f6,axiom,(
% 2.29/0.70    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.29/0.70  fof(f301,plain,(
% 2.29/0.70    spl5_9 | spl5_12),
% 2.29/0.70    inference(avatar_contradiction_clause,[],[f299])).
% 2.29/0.70  fof(f299,plain,(
% 2.29/0.70    $false | (spl5_9 | spl5_12)),
% 2.29/0.70    inference(unit_resulting_resolution,[],[f202,f297,f63])).
% 2.29/0.70  fof(f63,plain,(
% 2.29/0.70    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f37])).
% 2.29/0.70  fof(f297,plain,(
% 2.29/0.70    ( ! [X0] : (r2_hidden(X0,sK2)) ) | spl5_12),
% 2.29/0.70    inference(resolution,[],[f229,f111])).
% 2.29/0.70  fof(f111,plain,(
% 2.29/0.70    ( ! [X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.29/0.70    inference(equality_resolution,[],[f103])).
% 2.29/0.70  fof(f103,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.29/0.70    inference(definition_unfolding,[],[f67,f87])).
% 2.29/0.70  fof(f67,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f26])).
% 2.29/0.70  fof(f26,axiom,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.29/0.70  fof(f229,plain,(
% 2.29/0.70    ( ! [X0] : (~r1_tarski(k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | r2_hidden(X0,sK2)) ) | spl5_12),
% 2.29/0.70    inference(resolution,[],[f228,f98])).
% 2.29/0.70  fof(f228,plain,(
% 2.29/0.70    ( ! [X0] : (~r1_xboole_0(X0,sK2) | ~r1_tarski(k1_xboole_0,X0)) ) | spl5_12),
% 2.29/0.70    inference(resolution,[],[f224,f73])).
% 2.29/0.70  fof(f73,plain,(
% 2.29/0.70    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(cnf_transformation,[],[f39])).
% 2.29/0.70  fof(f39,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.29/0.70    inference(flattening,[],[f38])).
% 2.29/0.70  fof(f38,plain,(
% 2.29/0.70    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.29/0.70    inference(ennf_transformation,[],[f10])).
% 2.29/0.70  fof(f10,axiom,(
% 2.29/0.70    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.29/0.70  fof(f224,plain,(
% 2.29/0.70    ~r1_xboole_0(k1_xboole_0,sK2) | spl5_12),
% 2.29/0.70    inference(avatar_component_clause,[],[f223])).
% 2.29/0.70  fof(f227,plain,(
% 2.29/0.70    spl5_11 | ~spl5_12 | ~spl5_2 | ~spl5_5),
% 2.29/0.70    inference(avatar_split_clause,[],[f214,f131,f117,f223,f219])).
% 2.29/0.70  fof(f214,plain,(
% 2.29/0.70    ~r1_xboole_0(k1_xboole_0,sK2) | k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (~spl5_2 | ~spl5_5)),
% 2.29/0.70    inference(forward_demodulation,[],[f213,f118])).
% 2.29/0.70  fof(f213,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,sK2) | (~spl5_2 | ~spl5_5)),
% 2.29/0.70    inference(forward_demodulation,[],[f143,f118])).
% 2.29/0.70  fof(f143,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_xboole_0(sK1,sK2) | ~spl5_5),
% 2.29/0.70    inference(forward_demodulation,[],[f137,f72])).
% 2.29/0.70  fof(f137,plain,(
% 2.29/0.70    k1_xboole_0 = k5_xboole_0(k5_xboole_0(sK1,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r1_xboole_0(sK1,sK2) | ~spl5_5),
% 2.29/0.70    inference(superposition,[],[f100,f133])).
% 2.29/0.70  fof(f203,plain,(
% 2.29/0.70    ~spl5_9 | ~spl5_2 | spl5_7),
% 2.29/0.70    inference(avatar_split_clause,[],[f198,f154,f117,f200])).
% 2.29/0.70  fof(f198,plain,(
% 2.29/0.70    ~r1_tarski(k1_xboole_0,sK2) | (~spl5_2 | spl5_7)),
% 2.29/0.70    inference(backward_demodulation,[],[f156,f118])).
% 2.29/0.70  fof(f158,plain,(
% 2.29/0.70    spl5_2 | spl5_4 | ~spl5_6),
% 2.29/0.70    inference(avatar_split_clause,[],[f151,f147,f126,f117])).
% 2.29/0.70  fof(f147,plain,(
% 2.29/0.70    spl5_6 <=> r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.29/0.70  fof(f151,plain,(
% 2.29/0.70    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1 | ~spl5_6),
% 2.29/0.70    inference(resolution,[],[f149,f104])).
% 2.29/0.70  fof(f104,plain,(
% 2.29/0.70    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.29/0.70    inference(definition_unfolding,[],[f66,f87,f87])).
% 2.29/0.70  fof(f66,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f26])).
% 2.29/0.70  fof(f149,plain,(
% 2.29/0.70    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_6),
% 2.29/0.70    inference(avatar_component_clause,[],[f147])).
% 2.29/0.70  fof(f157,plain,(
% 2.29/0.70    ~spl5_7 | spl5_1 | ~spl5_5),
% 2.29/0.70    inference(avatar_split_clause,[],[f135,f131,f113,f154])).
% 2.29/0.70  fof(f113,plain,(
% 2.29/0.70    spl5_1 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.29/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.29/0.70  fof(f135,plain,(
% 2.29/0.70    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r1_tarski(sK1,sK2) | ~spl5_5),
% 2.29/0.70    inference(superposition,[],[f133,f99])).
% 2.29/0.70  fof(f99,plain,(
% 2.29/0.70    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.29/0.70    inference(definition_unfolding,[],[f57,f85])).
% 2.29/0.70  fof(f57,plain,(
% 2.29/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.29/0.70    inference(cnf_transformation,[],[f36])).
% 2.29/0.70  fof(f36,plain,(
% 2.29/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.29/0.70    inference(ennf_transformation,[],[f8])).
% 2.29/0.70  fof(f8,axiom,(
% 2.29/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.29/0.70  fof(f150,plain,(
% 2.29/0.70    spl5_6 | ~spl5_5),
% 2.29/0.70    inference(avatar_split_clause,[],[f141,f131,f147])).
% 2.29/0.70  fof(f141,plain,(
% 2.29/0.70    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~spl5_5),
% 2.29/0.70    inference(superposition,[],[f95,f133])).
% 2.29/0.70  fof(f95,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.29/0.70    inference(definition_unfolding,[],[f49,f85])).
% 2.29/0.70  fof(f49,plain,(
% 2.29/0.70    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.29/0.70    inference(cnf_transformation,[],[f11])).
% 2.29/0.70  fof(f11,axiom,(
% 2.29/0.70    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.29/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.29/0.70  fof(f134,plain,(
% 2.29/0.70    spl5_5),
% 2.29/0.70    inference(avatar_split_clause,[],[f89,f131])).
% 2.29/0.70  fof(f89,plain,(
% 2.29/0.70    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.29/0.70    inference(definition_unfolding,[],[f43,f87,f85])).
% 2.29/0.70  fof(f43,plain,(
% 2.29/0.70    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.29/0.70    inference(cnf_transformation,[],[f33])).
% 2.29/0.70  fof(f129,plain,(
% 2.29/0.70    ~spl5_3 | ~spl5_4),
% 2.29/0.70    inference(avatar_split_clause,[],[f92,f126,f122])).
% 2.29/0.70  fof(f92,plain,(
% 2.29/0.70    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 2.29/0.70    inference(definition_unfolding,[],[f40,f87])).
% 2.29/0.70  fof(f40,plain,(
% 2.29/0.70    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.29/0.70    inference(cnf_transformation,[],[f33])).
% 2.29/0.70  fof(f120,plain,(
% 2.29/0.70    ~spl5_1 | ~spl5_2),
% 2.29/0.70    inference(avatar_split_clause,[],[f91,f117,f113])).
% 2.29/0.70  fof(f91,plain,(
% 2.29/0.70    k1_xboole_0 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.29/0.70    inference(definition_unfolding,[],[f41,f87])).
% 2.29/0.70  fof(f41,plain,(
% 2.29/0.70    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.29/0.70    inference(cnf_transformation,[],[f33])).
% 2.29/0.70  % SZS output end Proof for theBenchmark
% 2.29/0.70  % (21879)------------------------------
% 2.29/0.70  % (21879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.70  % (21879)Termination reason: Refutation
% 2.29/0.70  
% 2.29/0.70  % (21879)Memory used [KB]: 11257
% 2.29/0.70  % (21879)Time elapsed: 0.251 s
% 2.29/0.70  % (21879)------------------------------
% 2.29/0.70  % (21879)------------------------------
% 2.29/0.70  % (21856)Success in time 0.333 s
%------------------------------------------------------------------------------
