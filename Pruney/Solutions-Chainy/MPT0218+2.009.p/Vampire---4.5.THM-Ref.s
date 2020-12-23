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
% DateTime   : Thu Dec  3 12:35:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 155 expanded)
%              Number of leaves         :   33 (  78 expanded)
%              Depth                    :    6
%              Number of atoms          :  213 ( 313 expanded)
%              Number of equality atoms :   57 (  96 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f727,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f55,f63,f69,f75,f84,f88,f92,f102,f110,f153,f175,f215,f275,f422,f659,f726])).

fof(f726,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_47 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_47 ),
    inference(subsumption_resolution,[],[f34,f724])).

fof(f724,plain,
    ( ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
    | ~ spl2_5
    | ~ spl2_47 ),
    inference(superposition,[],[f658,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_5
  <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f658,plain,
    ( ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl2_47 ),
    inference(avatar_component_clause,[],[f657])).

fof(f657,plain,
    ( spl2_47
  <=> ! [X1,X0,X2] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).

fof(f34,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f659,plain,
    ( spl2_47
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f560,f420,f67,f41,f657])).

fof(f41,plain,
    ( spl2_3
  <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f67,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f420,plain,
    ( spl2_38
  <=> ! [X1,X3,X0,X2] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f560,plain,
    ( ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))
    | ~ spl2_3
    | ~ spl2_9
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f558,f68])).

fof(f68,plain,
    ( ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f558,plain,
    ( ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2))
    | ~ spl2_3
    | ~ spl2_38 ),
    inference(superposition,[],[f421,f42])).

fof(f42,plain,
    ( ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f421,plain,
    ( ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f420])).

fof(f422,plain,
    ( spl2_38
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f349,f273,f73,f49,f420])).

fof(f73,plain,
    ( spl2_10
  <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f273,plain,
    ( spl2_29
  <=> ! [X1,X3,X0,X2,X4] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f349,plain,
    ( ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f346,f74])).

fof(f74,plain,
    ( ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f346,plain,
    ( ! [X2,X0,X3,X1] : r1_tarski(k2_tarski(X0,X1),k3_enumset1(X0,X0,X1,X2,X3))
    | ~ spl2_5
    | ~ spl2_29 ),
    inference(superposition,[],[f274,f50])).

fof(f274,plain,
    ( ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f273])).

fof(f275,plain,
    ( spl2_29
    | ~ spl2_9
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f266,f213,f82,f67,f273])).

fof(f82,plain,
    ( spl2_12
  <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f213,plain,
    ( spl2_24
  <=> ! [X1,X3,X5,X0,X2,X4] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f266,plain,
    ( ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))
    | ~ spl2_9
    | ~ spl2_12
    | ~ spl2_24 ),
    inference(forward_demodulation,[],[f263,f83])).

fof(f83,plain,
    ( ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f263,plain,
    ( ! [X4,X2,X0,X3,X1] : r1_tarski(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X2,X3,X4))
    | ~ spl2_9
    | ~ spl2_24 ),
    inference(superposition,[],[f214,f68])).

fof(f214,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f213])).

fof(f215,plain,
    ( spl2_24
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f178,f173,f151,f213])).

fof(f151,plain,
    ( spl2_19
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f173,plain,
    ( spl2_21
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f178,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(superposition,[],[f152,f174])).

fof(f174,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f152,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f151])).

fof(f175,plain,
    ( spl2_21
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f117,f108,f86,f73,f173])).

fof(f86,plain,
    ( spl2_13
  <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f108,plain,
    ( spl2_16
  <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f117,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl2_10
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f111,f74])).

fof(f111,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k2_tarski(X4,X5))
    | ~ spl2_13
    | ~ spl2_16 ),
    inference(superposition,[],[f109,f87])).

fof(f87,plain,
    ( ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f109,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f108])).

fof(f153,plain,
    ( spl2_19
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f103,f100,f53,f151])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f100,plain,
    ( spl2_15
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f103,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f101,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f101,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f100])).

fof(f110,plain,
    ( spl2_16
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f93,f90,f82,f108])).

fof(f90,plain,
    ( spl2_14
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f93,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(superposition,[],[f91,f83])).

fof(f91,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f102,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f71,f61,f45,f37,f100])).

fof(f37,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f45,plain,
    ( spl2_4
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f71,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f70,f38])).

fof(f38,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f70,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f62,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f62,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f92,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f30,f90])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f88,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f29,f86])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

fof(f84,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f28,f82])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f75,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f27,f73])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f69,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f67])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f61])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f55,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))
   => ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : ~ r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (9836)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (9836)Refutation not found, incomplete strategy% (9836)------------------------------
% 0.20/0.41  % (9836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (9836)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (9836)Memory used [KB]: 10490
% 0.20/0.41  % (9836)Time elapsed: 0.003 s
% 0.20/0.41  % (9836)------------------------------
% 0.20/0.41  % (9836)------------------------------
% 0.20/0.44  % (9830)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (9833)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (9835)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (9839)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (9830)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f727,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f55,f63,f69,f75,f84,f88,f92,f102,f110,f153,f175,f215,f275,f422,f659,f726])).
% 0.20/0.46  fof(f726,plain,(
% 0.20/0.46    spl2_1 | ~spl2_5 | ~spl2_47),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f725])).
% 0.20/0.46  fof(f725,plain,(
% 0.20/0.46    $false | (spl2_1 | ~spl2_5 | ~spl2_47)),
% 0.20/0.46    inference(subsumption_resolution,[],[f34,f724])).
% 0.20/0.46  fof(f724,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) ) | (~spl2_5 | ~spl2_47)),
% 0.20/0.46    inference(superposition,[],[f658,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) ) | ~spl2_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    spl2_5 <=> ! [X1,X0] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.46  fof(f658,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | ~spl2_47),
% 0.20/0.46    inference(avatar_component_clause,[],[f657])).
% 0.20/0.46  fof(f657,plain,(
% 0.20/0.46    spl2_47 <=> ! [X1,X0,X2] : r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_47])])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) | spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_1 <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f659,plain,(
% 0.20/0.46    spl2_47 | ~spl2_3 | ~spl2_9 | ~spl2_38),
% 0.20/0.46    inference(avatar_split_clause,[],[f560,f420,f67,f41,f657])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl2_3 <=> ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    spl2_9 <=> ! [X1,X0,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.46  fof(f420,plain,(
% 0.20/0.46    spl2_38 <=> ! [X1,X3,X0,X2] : r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.20/0.46  fof(f560,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k1_enumset1(X0,X1,X2))) ) | (~spl2_3 | ~spl2_9 | ~spl2_38)),
% 0.20/0.46    inference(forward_demodulation,[],[f558,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) ) | ~spl2_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f67])).
% 0.20/0.46  fof(f558,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X1,X2))) ) | (~spl2_3 | ~spl2_38)),
% 0.20/0.46    inference(superposition,[],[f421,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) ) | ~spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f41])).
% 0.20/0.46  fof(f421,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))) ) | ~spl2_38),
% 0.20/0.46    inference(avatar_component_clause,[],[f420])).
% 0.20/0.46  fof(f422,plain,(
% 0.20/0.46    spl2_38 | ~spl2_5 | ~spl2_10 | ~spl2_29),
% 0.20/0.46    inference(avatar_split_clause,[],[f349,f273,f73,f49,f420])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    spl2_10 <=> ! [X1,X3,X0,X2] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.46  fof(f273,plain,(
% 0.20/0.46    spl2_29 <=> ! [X1,X3,X0,X2,X4] : r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.20/0.46  fof(f349,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k2_enumset1(X0,X1,X2,X3))) ) | (~spl2_5 | ~spl2_10 | ~spl2_29)),
% 0.20/0.46    inference(forward_demodulation,[],[f346,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) ) | ~spl2_10),
% 0.20/0.46    inference(avatar_component_clause,[],[f73])).
% 0.20/0.46  fof(f346,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_tarski(X0,X1),k3_enumset1(X0,X0,X1,X2,X3))) ) | (~spl2_5 | ~spl2_29)),
% 0.20/0.46    inference(superposition,[],[f274,f50])).
% 0.20/0.46  fof(f274,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))) ) | ~spl2_29),
% 0.20/0.46    inference(avatar_component_clause,[],[f273])).
% 0.20/0.46  fof(f275,plain,(
% 0.20/0.46    spl2_29 | ~spl2_9 | ~spl2_12 | ~spl2_24),
% 0.20/0.46    inference(avatar_split_clause,[],[f266,f213,f82,f67,f273])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    spl2_12 <=> ! [X1,X3,X0,X2,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.46  fof(f213,plain,(
% 0.20/0.46    spl2_24 <=> ! [X1,X3,X5,X0,X2,X4] : r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.20/0.46  fof(f266,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k3_enumset1(X0,X1,X2,X3,X4))) ) | (~spl2_9 | ~spl2_12 | ~spl2_24)),
% 0.20/0.46    inference(forward_demodulation,[],[f263,f83])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) ) | ~spl2_12),
% 0.20/0.46    inference(avatar_component_clause,[],[f82])).
% 0.20/0.46  fof(f263,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (r1_tarski(k1_enumset1(X0,X1,X2),k4_enumset1(X0,X0,X1,X2,X3,X4))) ) | (~spl2_9 | ~spl2_24)),
% 0.20/0.46    inference(superposition,[],[f214,f68])).
% 0.20/0.46  fof(f214,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))) ) | ~spl2_24),
% 0.20/0.46    inference(avatar_component_clause,[],[f213])).
% 0.20/0.46  fof(f215,plain,(
% 0.20/0.46    spl2_24 | ~spl2_19 | ~spl2_21),
% 0.20/0.46    inference(avatar_split_clause,[],[f178,f173,f151,f213])).
% 0.20/0.46  fof(f151,plain,(
% 0.20/0.46    spl2_19 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    spl2_21 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tarski(k2_enumset1(X0,X1,X2,X3),k4_enumset1(X0,X1,X2,X3,X4,X5))) ) | (~spl2_19 | ~spl2_21)),
% 0.20/0.46    inference(superposition,[],[f152,f174])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | ~spl2_21),
% 0.20/0.46    inference(avatar_component_clause,[],[f173])).
% 0.20/0.46  fof(f152,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f151])).
% 0.20/0.46  fof(f175,plain,(
% 0.20/0.46    spl2_21 | ~spl2_10 | ~spl2_13 | ~spl2_16),
% 0.20/0.46    inference(avatar_split_clause,[],[f117,f108,f86,f73,f173])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    spl2_13 <=> ! [X1,X3,X5,X0,X2,X4] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.46  fof(f108,plain,(
% 0.20/0.46    spl2_16 <=> ! [X1,X3,X5,X0,X2,X4,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl2_10 | ~spl2_13 | ~spl2_16)),
% 0.20/0.46    inference(forward_demodulation,[],[f111,f74])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k2_tarski(X4,X5))) ) | (~spl2_13 | ~spl2_16)),
% 0.20/0.46    inference(superposition,[],[f109,f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) ) | ~spl2_13),
% 0.20/0.46    inference(avatar_component_clause,[],[f86])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | ~spl2_16),
% 0.20/0.46    inference(avatar_component_clause,[],[f108])).
% 0.20/0.46  fof(f153,plain,(
% 0.20/0.46    spl2_19 | ~spl2_6 | ~spl2_15),
% 0.20/0.46    inference(avatar_split_clause,[],[f103,f100,f53,f151])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl2_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.46  fof(f100,plain,(
% 0.20/0.46    spl2_15 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_6 | ~spl2_15)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f101,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl2_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f53])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl2_15),
% 0.20/0.46    inference(avatar_component_clause,[],[f100])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    spl2_16 | ~spl2_12 | ~spl2_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f93,f90,f82,f108])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    spl2_14 <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.46  fof(f93,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) ) | (~spl2_12 | ~spl2_14)),
% 0.20/0.46    inference(superposition,[],[f91,f83])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) ) | ~spl2_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f90])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    spl2_15 | ~spl2_2 | ~spl2_4 | ~spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f71,f61,f45,f37,f100])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl2_2 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl2_4 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl2_8 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl2_2 | ~spl2_4 | ~spl2_8)),
% 0.20/0.46    inference(forward_demodulation,[],[f70,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f37])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl2_4 | ~spl2_8)),
% 0.20/0.46    inference(superposition,[],[f62,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl2_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f45])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    spl2_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f90])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    spl2_13),
% 0.20/0.46    inference(avatar_split_clause,[],[f29,f86])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    spl2_12),
% 0.20/0.46    inference(avatar_split_clause,[],[f28,f82])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    spl2_10),
% 0.20/0.46    inference(avatar_split_clause,[],[f27,f73])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    spl2_9),
% 0.20/0.46    inference(avatar_split_clause,[],[f26,f67])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    spl2_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f23,f61])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.46  fof(f55,plain,(
% 0.20/0.46    spl2_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f53])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.46    inference(nnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl2_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f22,f49])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    spl2_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f21,f45])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f41])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f37])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~spl2_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f32])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) => ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1] : ~r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f12])).
% 0.20/0.46  fof(f12,conjecture,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (9830)------------------------------
% 0.20/0.46  % (9830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (9830)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (9830)Memory used [KB]: 6652
% 0.20/0.46  % (9830)Time elapsed: 0.055 s
% 0.20/0.46  % (9830)------------------------------
% 0.20/0.46  % (9830)------------------------------
% 0.20/0.47  % (9824)Success in time 0.111 s
%------------------------------------------------------------------------------
