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
% DateTime   : Thu Dec  3 12:31:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 187 expanded)
%              Number of leaves         :   27 (  87 expanded)
%              Depth                    :    7
%              Number of atoms          :  237 ( 409 expanded)
%              Number of equality atoms :   69 ( 137 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f694,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f46,f51,f55,f61,f65,f69,f75,f82,f86,f92,f144,f167,f195,f205,f232,f583,f627])).

fof(f627,plain,
    ( ~ spl3_3
    | ~ spl3_10
    | spl3_19
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_10
    | spl3_19
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f625,f204])).

fof(f204,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f625,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f590,f45])).

fof(f45,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f590,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_10
    | ~ spl3_34 ),
    inference(superposition,[],[f582,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f582,plain,
    ( ! [X27] : k4_xboole_0(sK0,X27) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f581])).

fof(f581,plain,
    ( spl3_34
  <=> ! [X27] : k4_xboole_0(sK0,X27) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f583,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f478,f230,f142,f58,f44,f581])).

fof(f58,plain,
    ( spl3_6
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f142,plain,
    ( spl3_14
  <=> ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f230,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f478,plain,
    ( ! [X27] : k4_xboole_0(sK0,X27) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f477,f143])).

fof(f143,plain,
    ( ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f477,plain,
    ( ! [X27] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X27))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f385,f45])).

fof(f385,plain,
    ( ! [X27] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X27))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))
    | ~ spl3_6
    | ~ spl3_23 ),
    inference(superposition,[],[f231,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f231,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f230])).

fof(f232,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f32,f230])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f26,f21,f21,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f205,plain,
    ( ~ spl3_19
    | ~ spl3_3
    | spl3_9
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f199,f192,f142,f72,f44,f202])).

fof(f72,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f192,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f199,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_3
    | spl3_9
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f74,f198])).

fof(f198,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f196,f45])).

fof(f196,plain,
    ( k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_14
    | ~ spl3_18 ),
    inference(superposition,[],[f143,f194])).

fof(f194,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f192])).

fof(f74,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f195,plain,
    ( spl3_18
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f178,f165,f79,f192])).

fof(f165,plain,
    ( spl3_16
  <=> ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f178,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(superposition,[],[f166,f81])).

fof(f166,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f167,plain,
    ( spl3_16
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f146,f142,f84,f165])).

fof(f84,plain,
    ( spl3_11
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f146,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(superposition,[],[f143,f85])).

fof(f85,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f144,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f130,f90,f58,f44,f142])).

fof(f90,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f130,plain,
    ( ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16)
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f109,f45])).

fof(f109,plain,
    ( ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X16)
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f91,f60])).

fof(f91,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f31,f90])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f21,f21])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f86,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f84])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f82,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f76,f67,f48,f79])).

fof(f48,plain,
    ( spl3_4
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f75,plain,
    ( ~ spl3_9
    | spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f70,f63,f34,f72])).

fof(f34,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f63,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f70,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f64,f36])).

fof(f36,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f67])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f56,f53,f39,f58])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f54,f41])).

fof(f41,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f18,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f44])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:50:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.42  % (23304)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (23304)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f694,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f37,f42,f46,f51,f55,f61,f65,f69,f75,f82,f86,f92,f144,f167,f195,f205,f232,f583,f627])).
% 0.21/0.45  fof(f627,plain,(
% 0.21/0.45    ~spl3_3 | ~spl3_10 | spl3_19 | ~spl3_34),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f626])).
% 0.21/0.45  fof(f626,plain,(
% 0.21/0.45    $false | (~spl3_3 | ~spl3_10 | spl3_19 | ~spl3_34)),
% 0.21/0.45    inference(subsumption_resolution,[],[f625,f204])).
% 0.21/0.45  fof(f204,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(sK0,sK0) | spl3_19),
% 0.21/0.45    inference(avatar_component_clause,[],[f202])).
% 0.21/0.45  fof(f202,plain,(
% 0.21/0.45    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.45  fof(f625,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_3 | ~spl3_10 | ~spl3_34)),
% 0.21/0.45    inference(forward_demodulation,[],[f590,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f590,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | (~spl3_10 | ~spl3_34)),
% 0.21/0.45    inference(superposition,[],[f582,f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | ~spl3_10),
% 0.21/0.45    inference(avatar_component_clause,[],[f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.45  fof(f582,plain,(
% 0.21/0.45    ( ! [X27] : (k4_xboole_0(sK0,X27) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))) ) | ~spl3_34),
% 0.21/0.45    inference(avatar_component_clause,[],[f581])).
% 0.21/0.45  fof(f581,plain,(
% 0.21/0.45    spl3_34 <=> ! [X27] : k4_xboole_0(sK0,X27) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.45  fof(f583,plain,(
% 0.21/0.45    spl3_34 | ~spl3_3 | ~spl3_6 | ~spl3_14 | ~spl3_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f478,f230,f142,f58,f44,f581])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    spl3_6 <=> k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    spl3_14 <=> ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.45  fof(f230,plain,(
% 0.21/0.45    spl3_23 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.45  fof(f478,plain,(
% 0.21/0.45    ( ! [X27] : (k4_xboole_0(sK0,X27) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))) ) | (~spl3_3 | ~spl3_6 | ~spl3_14 | ~spl3_23)),
% 0.21/0.45    inference(forward_demodulation,[],[f477,f143])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16)) ) | ~spl3_14),
% 0.21/0.45    inference(avatar_component_clause,[],[f142])).
% 0.21/0.45  fof(f477,plain,(
% 0.21/0.45    ( ! [X27] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X27))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))) ) | (~spl3_3 | ~spl3_6 | ~spl3_23)),
% 0.21/0.45    inference(forward_demodulation,[],[f385,f45])).
% 0.21/0.45  fof(f385,plain,(
% 0.21/0.45    ( ! [X27] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X27))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,X27)))) ) | (~spl3_6 | ~spl3_23)),
% 0.21/0.45    inference(superposition,[],[f231,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK2) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f58])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f230])).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    spl3_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f230])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f26,f21,f21,f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    ~spl3_19 | ~spl3_3 | spl3_9 | ~spl3_14 | ~spl3_18),
% 0.21/0.45    inference(avatar_split_clause,[],[f199,f192,f142,f72,f44,f202])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl3_9 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.45  fof(f192,plain,(
% 0.21/0.45    spl3_18 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.45  fof(f199,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_3 | spl3_9 | ~spl3_14 | ~spl3_18)),
% 0.21/0.45    inference(backward_demodulation,[],[f74,f198])).
% 0.21/0.45  fof(f198,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_14 | ~spl3_18)),
% 0.21/0.45    inference(forward_demodulation,[],[f196,f45])).
% 0.21/0.45  fof(f196,plain,(
% 0.21/0.45    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_14 | ~spl3_18)),
% 0.21/0.45    inference(superposition,[],[f143,f194])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | ~spl3_18),
% 0.21/0.45    inference(avatar_component_clause,[],[f192])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f72])).
% 0.21/0.45  fof(f195,plain,(
% 0.21/0.45    spl3_18 | ~spl3_10 | ~spl3_16),
% 0.21/0.45    inference(avatar_split_clause,[],[f178,f165,f79,f192])).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    spl3_16 <=> ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.45  fof(f178,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK2,sK1)) | (~spl3_10 | ~spl3_16)),
% 0.21/0.45    inference(superposition,[],[f166,f81])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) ) | ~spl3_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f165])).
% 0.21/0.45  fof(f167,plain,(
% 0.21/0.45    spl3_16 | ~spl3_11 | ~spl3_14),
% 0.21/0.45    inference(avatar_split_clause,[],[f146,f142,f84,f165])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl3_11 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK2,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(X0,sK2))))) ) | (~spl3_11 | ~spl3_14)),
% 0.21/0.45    inference(superposition,[],[f143,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f144,plain,(
% 0.21/0.45    spl3_14 | ~spl3_3 | ~spl3_6 | ~spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f130,f90,f58,f44,f142])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(sK0,X16)) ) | (~spl3_3 | ~spl3_6 | ~spl3_12)),
% 0.21/0.45    inference(forward_demodulation,[],[f109,f45])).
% 0.21/0.45  fof(f109,plain,(
% 0.21/0.45    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X16))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X16)) ) | (~spl3_6 | ~spl3_12)),
% 0.21/0.45    inference(superposition,[],[f91,f60])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f90])).
% 0.21/0.45  fof(f92,plain,(
% 0.21/0.45    spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f90])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f25,f21,f21])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f28,f84])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl3_10 | ~spl3_4 | ~spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f76,f67,f48,f79])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl3_4 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl3_8 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) | (~spl3_4 | ~spl3_8)),
% 0.21/0.45    inference(resolution,[],[f68,f50])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f48])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f67])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    ~spl3_9 | spl3_1 | ~spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f70,f63,f34,f72])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (spl3_1 | ~spl3_7)),
% 0.21/0.45    inference(resolution,[],[f64,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1) | spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f34])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f63])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f30,f67])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f21])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.45    inference(nnf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f29,f63])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f23,f21])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f15])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    spl3_6 | ~spl3_2 | ~spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f56,f53,f39,f58])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_2 <=> r1_tarski(sK0,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl3_5 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_5)),
% 0.21/0.45    inference(resolution,[],[f54,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    r1_tarski(sK0,sK2) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f39])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f53])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f48])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.45    inference(definition_unfolding,[],[f18,f21])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f19,f44])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    r1_tarski(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    ~spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f16,f34])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (23304)------------------------------
% 0.21/0.45  % (23304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (23304)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (23304)Memory used [KB]: 7036
% 0.21/0.45  % (23304)Time elapsed: 0.053 s
% 0.21/0.45  % (23304)------------------------------
% 0.21/0.45  % (23304)------------------------------
% 0.21/0.45  % (23296)Success in time 0.098 s
%------------------------------------------------------------------------------
