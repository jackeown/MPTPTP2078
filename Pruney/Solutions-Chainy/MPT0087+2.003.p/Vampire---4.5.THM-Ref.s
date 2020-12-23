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
% DateTime   : Thu Dec  3 12:31:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 138 expanded)
%              Number of leaves         :   27 (  65 expanded)
%              Depth                    :    6
%              Number of atoms          :  199 ( 300 expanded)
%              Number of equality atoms :   61 ( 100 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f388,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f47,f55,f59,f63,f71,f75,f79,f83,f119,f151,f163,f283,f312,f366,f371,f386])).

fof(f386,plain,
    ( ~ spl3_1
    | spl3_16
    | ~ spl3_18
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | ~ spl3_1
    | spl3_16
    | ~ spl3_18
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f33,f384])).

fof(f384,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_16
    | ~ spl3_18
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f333,f380])).

fof(f380,plain,
    ( ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)
    | ~ spl3_18
    | ~ spl3_30 ),
    inference(superposition,[],[f370,f162])).

fof(f162,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_18
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f370,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl3_30
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f333,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | spl3_16
    | ~ spl3_27 ),
    inference(superposition,[],[f150,f311])).

fof(f311,plain,
    ( ! [X4,X2,X3] :
        ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl3_27
  <=> ! [X3,X2,X4] :
        ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_xboole_0(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f150,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_16
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f371,plain,
    ( spl3_30
    | ~ spl3_26
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f367,f364,f281,f369])).

fof(f281,plain,
    ( spl3_26
  <=> ! [X1,X2] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f364,plain,
    ( spl3_29
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f367,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_26
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f365,f282])).

fof(f282,plain,
    ( ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f281])).

fof(f365,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f364])).

fof(f366,plain,
    ( spl3_29
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f100,f73,f69,f53,f364])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f100,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f97,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f97,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(superposition,[],[f70,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f70,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f312,plain,
    ( spl3_27
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f121,f117,f57,f310])).

fof(f57,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f117,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f121,plain,
    ( ! [X4,X2,X3] :
        ( k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_xboole_0(X2,X3) )
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f118,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f118,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f117])).

fof(f283,plain,
    ( spl3_26
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f114,f81,f77,f73,f281])).

fof(f77,plain,
    ( spl3_11
  <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f114,plain,
    ( ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f110,f99])).

fof(f99,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f96,f78])).

fof(f78,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f96,plain,
    ( ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ spl3_10 ),
    inference(superposition,[],[f74,f74])).

fof(f110,plain,
    ( ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = X1
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(superposition,[],[f82,f74])).

fof(f82,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f163,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f53,f45,f161])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f64,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(superposition,[],[f54,f46])).

fof(f46,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f151,plain,
    ( ~ spl3_16
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f90,f61,f36,f148])).

fof(f36,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f61,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f90,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f38,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f119,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f29,f117])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f83,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f26,f81])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f79,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f25,f77])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f75,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f23,f69])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f63,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f61])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f59,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f39,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f31])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:32:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (22289)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (22286)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (22296)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (22295)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (22291)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (22292)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (22290)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (22287)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (22300)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (22299)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (22291)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (22297)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (22288)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (22294)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f388,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f34,f39,f47,f55,f59,f63,f71,f75,f79,f83,f119,f151,f163,f283,f312,f366,f371,f386])).
% 0.21/0.52  fof(f386,plain,(
% 0.21/0.52    ~spl3_1 | spl3_16 | ~spl3_18 | ~spl3_27 | ~spl3_30),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f385])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    $false | (~spl3_1 | spl3_16 | ~spl3_18 | ~spl3_27 | ~spl3_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f33,f384])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,sK1) | (spl3_16 | ~spl3_18 | ~spl3_27 | ~spl3_30)),
% 0.21/0.52    inference(subsumption_resolution,[],[f333,f380])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)) ) | (~spl3_18 | ~spl3_30)),
% 0.21/0.52    inference(superposition,[],[f370,f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f161])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl3_18 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f369])).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    spl3_30 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.52  fof(f333,plain,(
% 0.21/0.52    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK2) | ~r1_xboole_0(sK0,sK1) | (spl3_16 | ~spl3_27)),
% 0.21/0.52    inference(superposition,[],[f150,f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X2,X3)) ) | ~spl3_27),
% 0.21/0.52    inference(avatar_component_clause,[],[f310])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    spl3_27 <=> ! [X3,X2,X4] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X2,X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl3_16 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    spl3_30 | ~spl3_26 | ~spl3_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f367,f364,f281,f369])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    spl3_26 <=> ! [X1,X2] : k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    spl3_29 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | (~spl3_26 | ~spl3_29)),
% 0.21/0.52    inference(forward_demodulation,[],[f365,f282])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) ) | ~spl3_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f281])).
% 0.21/0.52  fof(f365,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f364])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    spl3_29 | ~spl3_6 | ~spl3_9 | ~spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f100,f73,f69,f53,f364])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl3_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl3_9 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    spl3_10 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl3_6 | ~spl3_9 | ~spl3_10)),
% 0.21/0.52    inference(forward_demodulation,[],[f97,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f53])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_9 | ~spl3_10)),
% 0.21/0.52    inference(superposition,[],[f70,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f73])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f69])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    spl3_27 | ~spl3_7 | ~spl3_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f121,f117,f57,f310])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    spl3_7 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl3_14 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_xboole_0(X2,X3)) ) | (~spl3_7 | ~spl3_14)),
% 0.21/0.52    inference(superposition,[],[f118,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f57])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f117])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    spl3_26 | ~spl3_10 | ~spl3_11 | ~spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f114,f81,f77,f73,f281])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl3_11 <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl3_12 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) ) | (~spl3_10 | ~spl3_11 | ~spl3_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f110,f99])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl3_10 | ~spl3_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f96,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) ) | ~spl3_10),
% 0.21/0.52    inference(superposition,[],[f74,f74])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,k4_xboole_0(X1,X2)),k3_xboole_0(X1,X2)) = X1) ) | (~spl3_10 | ~spl3_12)),
% 0.21/0.52    inference(superposition,[],[f82,f74])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl3_18 | ~spl3_4 | ~spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f64,f53,f45,f161])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl3_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_4 | ~spl3_6)),
% 0.21/0.52    inference(superposition,[],[f54,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f45])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ~spl3_16 | spl3_2 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f90,f61,f36,f148])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl3_8 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    k1_xboole_0 != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_2 | ~spl3_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f38,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f36])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    spl3_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f117])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f26,f81])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f77])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f73])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f69])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f28,f61])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f27,f57])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f18,f36])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f11])).
% 0.21/0.52  fof(f11,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f31])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    r1_xboole_0(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22291)------------------------------
% 0.21/0.52  % (22291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22291)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22291)Memory used [KB]: 6396
% 0.21/0.52  % (22291)Time elapsed: 0.071 s
% 0.21/0.52  % (22291)------------------------------
% 0.21/0.52  % (22291)------------------------------
% 0.21/0.52  % (22285)Success in time 0.157 s
%------------------------------------------------------------------------------
