%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 241 expanded)
%              Number of leaves         :   27 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 ( 401 expanded)
%              Number of equality atoms :   81 ( 192 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1933,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f69,f75,f82,f122,f127,f134,f217,f222,f229,f243,f318,f336,f1927])).

fof(f1927,plain,
    ( ~ spl3_4
    | spl3_6
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f1926])).

fof(f1926,plain,
    ( $false
    | ~ spl3_4
    | spl3_6
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1912,f81])).

fof(f81,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_6
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1912,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f1885,f68])).

fof(f68,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_4
  <=> sK0 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1885,plain,
    ( ! [X4] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK1),sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f1872,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1872,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X0),sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f1863,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f83,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f83,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f27,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1863,plain,
    ( ! [X0] : k3_xboole_0(k3_xboole_0(sK1,X0),sK2) = k4_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0))
    | ~ spl3_9 ),
    inference(superposition,[],[f27,f1786])).

fof(f1786,plain,
    ( ! [X18] : k3_xboole_0(sK1,X18) = k4_xboole_0(k3_xboole_0(sK1,X18),sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f1704,f27])).

fof(f1704,plain,
    ( ! [X18] : k4_xboole_0(sK1,k4_xboole_0(sK1,X18)) = k4_xboole_0(k3_xboole_0(sK1,X18),sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f103,f157])).

fof(f157,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))
    | ~ spl3_9 ),
    inference(superposition,[],[f136,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f136,plain,
    ( ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)
    | ~ spl3_9 ),
    inference(superposition,[],[f32,f133])).

fof(f133,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl3_9
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f103,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k3_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f32,f27])).

fof(f336,plain,
    ( spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f329,f315,f333])).

fof(f333,plain,
    ( spl3_15
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f315,plain,
    ( spl3_14
  <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f329,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f328,f144])).

fof(f144,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f92,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f25,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f92,plain,(
    ! [X6] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f28,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f26,f22])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f328,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK1)
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f327,f48])).

fof(f327,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f326,f104])).

fof(f104,plain,(
    ! [X6,X5] : k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f32,f85])).

fof(f326,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f325,f25])).

fof(f325,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f320,f32])).

fof(f320,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))
    | ~ spl3_14 ),
    inference(superposition,[],[f89,f317])).

fof(f317,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f315])).

fof(f89,plain,(
    ! [X2,X1] : k2_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1 ),
    inference(superposition,[],[f28,f26])).

fof(f318,plain,
    ( spl3_14
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f302,f66,f315])).

fof(f302,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f284,f85])).

fof(f284,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f84,f68])).

fof(f84,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f27,f27])).

fof(f243,plain,
    ( spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f238,f226,f240])).

fof(f240,plain,
    ( spl3_13
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f226,plain,
    ( spl3_12
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f238,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK1)
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f234,f85])).

fof(f234,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl3_12 ),
    inference(superposition,[],[f27,f228])).

fof(f228,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f226])).

fof(f229,plain,
    ( spl3_12
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f223,f219,f226])).

fof(f219,plain,
    ( spl3_11
  <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f223,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f221,f48])).

fof(f221,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f219])).

fof(f222,plain,
    ( spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f192,f72,f219])).

fof(f72,plain,
    ( spl3_5
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f192,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f89,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f217,plain,
    ( spl3_10
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f191,f66,f214])).

fof(f214,plain,
    ( spl3_10
  <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f191,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_4 ),
    inference(superposition,[],[f89,f68])).

fof(f134,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f128,f124,f131])).

fof(f124,plain,
    ( spl3_8
  <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f128,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f126,f48])).

fof(f126,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f94,f72,f124])).

fof(f94,plain,
    ( sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f28,f74])).

fof(f122,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f93,f66,f119])).

fof(f119,plain,
    ( spl3_7
  <=> sK0 = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f93,plain,
    ( sK0 = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f28,f68])).

fof(f82,plain,
    ( ~ spl3_6
    | spl3_3 ),
    inference(avatar_split_clause,[],[f76,f44,f79])).

fof(f44,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( k1_xboole_0 != k3_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f75,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f70,f39,f72])).

fof(f39,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f64,f34,f66])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f64,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f29,f36])).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (742)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.43  % (758)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (747)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (753)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (743)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (745)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (744)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (757)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (755)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (749)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (748)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (751)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (750)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (759)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (754)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (760)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (742)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f1933,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f37,f42,f47,f69,f75,f82,f122,f127,f134,f217,f222,f229,f243,f318,f336,f1927])).
% 0.22/0.51  fof(f1927,plain,(
% 0.22/0.51    ~spl3_4 | spl3_6 | ~spl3_9),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f1926])).
% 0.22/0.51  fof(f1926,plain,(
% 0.22/0.51    $false | (~spl3_4 | spl3_6 | ~spl3_9)),
% 0.22/0.51    inference(subsumption_resolution,[],[f1912,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl3_6 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.51  fof(f1912,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_4 | ~spl3_9)),
% 0.22/0.51    inference(superposition,[],[f1885,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    spl3_4 <=> sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.51  fof(f1885,plain,(
% 0.22/0.51    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK1),sK2)) ) | ~spl3_9),
% 0.22/0.51    inference(superposition,[],[f1872,f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.51  fof(f1872,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X0),sK2)) ) | ~spl3_9),
% 0.22/0.51    inference(forward_demodulation,[],[f1863,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f83,f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(superposition,[],[f27,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.51  fof(f1863,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(k3_xboole_0(sK1,X0),sK2) = k4_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK1,X0))) ) | ~spl3_9),
% 0.22/0.51    inference(superposition,[],[f27,f1786])).
% 0.22/0.51  fof(f1786,plain,(
% 0.22/0.51    ( ! [X18] : (k3_xboole_0(sK1,X18) = k4_xboole_0(k3_xboole_0(sK1,X18),sK2)) ) | ~spl3_9),
% 0.22/0.51    inference(forward_demodulation,[],[f1704,f27])).
% 0.22/0.51  fof(f1704,plain,(
% 0.22/0.51    ( ! [X18] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X18)) = k4_xboole_0(k3_xboole_0(sK1,X18),sK2)) ) | ~spl3_9),
% 0.22/0.51    inference(superposition,[],[f103,f157])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(X0,sK2))) ) | ~spl3_9),
% 0.22/0.51    inference(superposition,[],[f136,f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK1,X0)) ) | ~spl3_9),
% 0.22/0.51    inference(superposition,[],[f32,f133])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    spl3_9 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.51  fof(f103,plain,(
% 0.22/0.51    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(k4_xboole_0(X2,X3),X4)) = k4_xboole_0(k3_xboole_0(X2,X3),X4)) )),
% 0.22/0.51    inference(superposition,[],[f32,f27])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    spl3_15 | ~spl3_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f329,f315,f333])).
% 0.22/0.51  fof(f333,plain,(
% 0.22/0.51    spl3_15 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    spl3_14 <=> k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_14),
% 0.22/0.51    inference(forward_demodulation,[],[f328,f144])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.22/0.51    inference(superposition,[],[f92,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.51    inference(superposition,[],[f25,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X6] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X6))) )),
% 0.22/0.51    inference(superposition,[],[f28,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(superposition,[],[f26,f22])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) = k4_xboole_0(k1_xboole_0,sK1) | ~spl3_14),
% 0.22/0.51    inference(forward_demodulation,[],[f327,f48])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)) | ~spl3_14),
% 0.22/0.51    inference(forward_demodulation,[],[f326,f104])).
% 0.22/0.51  fof(f104,plain,(
% 0.22/0.51    ( ! [X6,X5] : (k4_xboole_0(k1_xboole_0,X6) = k4_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 0.22/0.51    inference(superposition,[],[f32,f85])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) | ~spl3_14),
% 0.22/0.51    inference(forward_demodulation,[],[f325,f25])).
% 0.22/0.51  fof(f325,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) | ~spl3_14),
% 0.22/0.51    inference(forward_demodulation,[],[f320,f32])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    k4_xboole_0(sK0,sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) | ~spl3_14),
% 0.22/0.51    inference(superposition,[],[f89,f317])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f315])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X2,X1),k4_xboole_0(X1,X2)) = X1) )),
% 0.22/0.51    inference(superposition,[],[f28,f26])).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    spl3_14 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f302,f66,f315])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_4),
% 0.22/0.51    inference(forward_demodulation,[],[f284,f85])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK0) | ~spl3_4),
% 0.22/0.51    inference(superposition,[],[f84,f68])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 0.22/0.51    inference(superposition,[],[f27,f27])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    spl3_13 | ~spl3_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f238,f226,f240])).
% 0.22/0.51  fof(f240,plain,(
% 0.22/0.51    spl3_13 <=> k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    spl3_12 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK2,sK1) | ~spl3_12),
% 0.22/0.51    inference(forward_demodulation,[],[f234,f85])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl3_12),
% 0.22/0.51    inference(superposition,[],[f27,f228])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f226])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    spl3_12 | ~spl3_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f223,f219,f226])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    spl3_11 <=> sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    sK2 = k4_xboole_0(sK2,sK1) | ~spl3_11),
% 0.22/0.51    inference(superposition,[],[f221,f48])).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f219])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    spl3_11 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f192,f72,f219])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    spl3_5 <=> k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK1)) | ~spl3_5),
% 0.22/0.51    inference(superposition,[],[f89,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f72])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    spl3_10 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f191,f66,f214])).
% 0.22/0.51  fof(f214,plain,(
% 0.22/0.51    spl3_10 <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl3_4),
% 0.22/0.51    inference(superposition,[],[f89,f68])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    spl3_9 | ~spl3_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f128,f124,f131])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    spl3_8 <=> sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_8),
% 0.22/0.51    inference(superposition,[],[f126,f48])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f124])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    spl3_8 | ~spl3_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f94,f72,f124])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.22/0.51    inference(superposition,[],[f28,f74])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    spl3_7 | ~spl3_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f93,f66,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl3_7 <=> sK0 = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    sK0 = k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_4),
% 0.22/0.51    inference(superposition,[],[f28,f68])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ~spl3_6 | spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f76,f44,f79])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    k1_xboole_0 != k3_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.51    inference(resolution,[],[f31,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f44])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    spl3_5 | ~spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f70,f39,f72])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.51    inference(resolution,[],[f30,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f39])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    spl3_4 | ~spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f34,f66])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    sK0 = k3_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.51    inference(resolution,[],[f29,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f34])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ~spl3_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f21,f44])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    inference(negated_conjecture,[],[f11])).
% 0.22/0.51  fof(f11,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    spl3_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f20,f39])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    r1_xboole_0(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    spl3_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f19,f34])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (742)------------------------------
% 0.22/0.51  % (742)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (742)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (742)Memory used [KB]: 7419
% 0.22/0.51  % (742)Time elapsed: 0.084 s
% 0.22/0.51  % (742)------------------------------
% 0.22/0.51  % (742)------------------------------
% 0.22/0.51  % (741)Success in time 0.148 s
%------------------------------------------------------------------------------
