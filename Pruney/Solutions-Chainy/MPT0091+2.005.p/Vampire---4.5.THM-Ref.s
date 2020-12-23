%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:39 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 207 expanded)
%              Number of leaves         :   19 (  81 expanded)
%              Depth                    :   18
%              Number of atoms          :  176 ( 384 expanded)
%              Number of equality atoms :   52 ( 147 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1454,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f71,f100,f101,f102,f131,f177,f224,f1410])).

fof(f1410,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f1409,f221,f91,f86,f128])).

fof(f128,plain,
    ( spl3_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f86,plain,
    ( spl3_7
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f91,plain,
    ( spl3_8
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f221,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f1409,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1408,f174])).

fof(f174,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f142,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f142,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f46,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f46,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f20,f19])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1408,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK0)
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1407,f258])).

fof(f258,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f50,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f20,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1407,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1406,f19])).

fof(f1406,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1405,f174])).

fof(f1405,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f1373,f93])).

fof(f93,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f91])).

fof(f1373,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(superposition,[],[f607,f88])).

fof(f88,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f607,plain,
    ( ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X20))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X20)))
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f606,f19])).

fof(f606,plain,
    ( ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X20))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X20)))
    | ~ spl3_8
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f547,f223])).

fof(f223,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f547,plain,
    ( ! [X20] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X20))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),X20)))
    | ~ spl3_8 ),
    inference(superposition,[],[f198,f93])).

fof(f198,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X5,X6))))))) ),
    inference(forward_demodulation,[],[f197,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f21,f21])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f197,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))))) ),
    inference(forward_demodulation,[],[f196,f30])).

fof(f196,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6))) ),
    inference(forward_demodulation,[],[f195,f30])).

fof(f195,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))))),X6) ),
    inference(forward_demodulation,[],[f187,f30])).

fof(f187,plain,(
    ! [X6,X4,X5,X3] : k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6) ),
    inference(superposition,[],[f30,f30])).

fof(f224,plain,
    ( spl3_19
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f219,f165,f96,f221])).

fof(f96,plain,
    ( spl3_9
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f165,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f219,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_9
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f167,f98])).

fof(f98,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f167,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f177,plain,
    ( spl3_17
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f151,f37,f165])).

fof(f37,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f151,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f29,f39])).

fof(f39,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f131,plain,
    ( ~ spl3_13
    | spl3_3 ),
    inference(avatar_split_clause,[],[f119,f42,f128])).

fof(f42,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f119,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f102,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f84,f62,f86])).

fof(f62,plain,
    ( spl3_5
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f84,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f25,f64])).

fof(f64,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f101,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f83,f32,f91])).

fof(f32,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f100,plain,
    ( spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f82,f37,f96])).

fof(f82,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f25,f39])).

fof(f71,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f37,f62])).

fof(f52,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f22,f39])).

fof(f45,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f42])).

fof(f16,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
          & r1_xboole_0(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f32])).

fof(f18,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:44:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.23/0.50  % (1797)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.50  % (1787)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (1789)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.51  % (1786)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.51  % (1795)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.51  % (1791)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.51  % (1792)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.51  % (1790)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.52  % (1794)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.52  % (1799)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.52  % (1800)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.53  % (1798)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.54  % (1784)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.54  % (1790)Refutation found. Thanks to Tanya!
% 0.23/0.54  % SZS status Theorem for theBenchmark
% 0.23/0.55  % (1801)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.55  % (1793)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f1454,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(avatar_sat_refutation,[],[f35,f40,f45,f71,f100,f101,f102,f131,f177,f224,f1410])).
% 0.23/0.55  fof(f1410,plain,(
% 0.23/0.55    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_19),
% 0.23/0.55    inference(avatar_split_clause,[],[f1409,f221,f91,f86,f128])).
% 0.23/0.55  fof(f128,plain,(
% 0.23/0.55    spl3_13 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.23/0.55  fof(f86,plain,(
% 0.23/0.55    spl3_7 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.55  fof(f91,plain,(
% 0.23/0.55    spl3_8 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.55  fof(f221,plain,(
% 0.23/0.55    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.23/0.55  fof(f1409,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f1408,f174])).
% 0.23/0.55  fof(f174,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f142,f19])).
% 0.23/0.55  fof(f19,plain,(
% 0.23/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f3])).
% 0.23/0.55  fof(f3,axiom,(
% 0.23/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.55  fof(f142,plain,(
% 0.23/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f46,f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(definition_unfolding,[],[f23,f21])).
% 0.23/0.55  fof(f21,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.55    inference(cnf_transformation,[],[f4])).
% 0.23/0.55  fof(f4,axiom,(
% 0.23/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f14])).
% 0.23/0.55  fof(f14,plain,(
% 0.23/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.23/0.55    inference(nnf_transformation,[],[f1])).
% 0.23/0.55  fof(f1,axiom,(
% 0.23/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.23/0.55  fof(f46,plain,(
% 0.23/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.55    inference(superposition,[],[f20,f19])).
% 0.23/0.55  fof(f20,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f6])).
% 0.23/0.55  fof(f6,axiom,(
% 0.23/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.23/0.55  fof(f1408,plain,(
% 0.23/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK0) | (~spl3_7 | ~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f1407,f258])).
% 0.23/0.55  fof(f258,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f50,f25])).
% 0.23/0.55  fof(f25,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f15])).
% 0.23/0.55  fof(f15,plain,(
% 0.23/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.23/0.55    inference(nnf_transformation,[],[f7])).
% 0.23/0.55  fof(f7,axiom,(
% 0.23/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.23/0.55  fof(f50,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f20,f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f11])).
% 0.23/0.55  fof(f11,plain,(
% 0.23/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f2])).
% 0.23/0.55  fof(f2,axiom,(
% 0.23/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.23/0.55  fof(f1407,plain,(
% 0.23/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | (~spl3_7 | ~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f1406,f19])).
% 0.23/0.55  fof(f1406,plain,(
% 0.23/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))) | (~spl3_7 | ~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f1405,f174])).
% 0.23/0.55  fof(f1405,plain,(
% 0.23/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)))) | (~spl3_7 | ~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f1373,f93])).
% 0.23/0.55  fof(f93,plain,(
% 0.23/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 0.23/0.55    inference(avatar_component_clause,[],[f91])).
% 0.23/0.55  fof(f1373,plain,(
% 0.23/0.55    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))))) | (~spl3_7 | ~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(superposition,[],[f607,f88])).
% 0.23/0.55  fof(f88,plain,(
% 0.23/0.55    sK2 = k4_xboole_0(sK2,sK0) | ~spl3_7),
% 0.23/0.55    inference(avatar_component_clause,[],[f86])).
% 0.23/0.55  fof(f607,plain,(
% 0.23/0.55    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X20))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,X20)))) ) | (~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f606,f19])).
% 0.23/0.55  fof(f606,plain,(
% 0.23/0.55    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X20))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k1_xboole_0),X20)))) ) | (~spl3_8 | ~spl3_19)),
% 0.23/0.55    inference(forward_demodulation,[],[f547,f223])).
% 0.23/0.55  fof(f223,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_19),
% 0.23/0.55    inference(avatar_component_clause,[],[f221])).
% 0.23/0.55  fof(f547,plain,(
% 0.23/0.55    ( ! [X20] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK2,X20))))))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK0)),X20)))) ) | ~spl3_8),
% 0.23/0.55    inference(superposition,[],[f198,f93])).
% 0.23/0.55  fof(f198,plain,(
% 0.23/0.55    ( ! [X6,X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X5,X6)))))))) )),
% 0.23/0.55    inference(forward_demodulation,[],[f197,f30])).
% 0.23/0.55  fof(f30,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.23/0.55    inference(definition_unfolding,[],[f27,f21,f21])).
% 0.23/0.55  fof(f27,plain,(
% 0.23/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f5])).
% 0.23/0.55  fof(f5,axiom,(
% 0.23/0.55    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.23/0.55  fof(f197,plain,(
% 0.23/0.55    ( ! [X6,X4,X5,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6)))))) )),
% 0.23/0.55    inference(forward_demodulation,[],[f196,f30])).
% 0.23/0.55  fof(f196,plain,(
% 0.23/0.55    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))) = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6)))) )),
% 0.23/0.55    inference(forward_demodulation,[],[f195,f30])).
% 0.23/0.55  fof(f195,plain,(
% 0.23/0.55    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))))),X6)) )),
% 0.23/0.55    inference(forward_demodulation,[],[f187,f30])).
% 0.23/0.55  fof(f187,plain,(
% 0.23/0.55    ( ! [X6,X4,X5,X3] : (k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X5,X6))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X5)))),X6)) )),
% 0.23/0.55    inference(superposition,[],[f30,f30])).
% 0.23/0.55  fof(f224,plain,(
% 0.23/0.55    spl3_19 | ~spl3_9 | ~spl3_17),
% 0.23/0.55    inference(avatar_split_clause,[],[f219,f165,f96,f221])).
% 0.23/0.55  fof(f96,plain,(
% 0.23/0.55    spl3_9 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.55  fof(f165,plain,(
% 0.23/0.55    spl3_17 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.55  fof(f219,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_9 | ~spl3_17)),
% 0.23/0.55    inference(forward_demodulation,[],[f167,f98])).
% 0.23/0.55  fof(f98,plain,(
% 0.23/0.55    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_9),
% 0.23/0.55    inference(avatar_component_clause,[],[f96])).
% 0.23/0.55  fof(f167,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_17),
% 0.23/0.55    inference(avatar_component_clause,[],[f165])).
% 0.23/0.55  fof(f177,plain,(
% 0.23/0.55    spl3_17 | ~spl3_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f151,f37,f165])).
% 0.23/0.55  fof(f37,plain,(
% 0.23/0.55    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.55  fof(f151,plain,(
% 0.23/0.55    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl3_2),
% 0.23/0.55    inference(resolution,[],[f29,f39])).
% 0.23/0.55  fof(f39,plain,(
% 0.23/0.55    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.23/0.55    inference(avatar_component_clause,[],[f37])).
% 0.23/0.55  fof(f131,plain,(
% 0.23/0.55    ~spl3_13 | spl3_3),
% 0.23/0.55    inference(avatar_split_clause,[],[f119,f42,f128])).
% 0.23/0.55  fof(f42,plain,(
% 0.23/0.55    spl3_3 <=> r1_xboole_0(sK0,sK1)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.55  fof(f119,plain,(
% 0.23/0.55    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl3_3),
% 0.23/0.55    inference(unit_resulting_resolution,[],[f44,f28])).
% 0.23/0.55  fof(f28,plain,(
% 0.23/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.23/0.55    inference(definition_unfolding,[],[f24,f21])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.23/0.55    inference(cnf_transformation,[],[f14])).
% 0.23/0.55  fof(f44,plain,(
% 0.23/0.55    ~r1_xboole_0(sK0,sK1) | spl3_3),
% 0.23/0.55    inference(avatar_component_clause,[],[f42])).
% 0.23/0.55  fof(f102,plain,(
% 0.23/0.55    spl3_7 | ~spl3_5),
% 0.23/0.55    inference(avatar_split_clause,[],[f84,f62,f86])).
% 0.23/0.55  fof(f62,plain,(
% 0.23/0.55    spl3_5 <=> r1_xboole_0(sK2,sK0)),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.55  fof(f84,plain,(
% 0.23/0.55    sK2 = k4_xboole_0(sK2,sK0) | ~spl3_5),
% 0.23/0.55    inference(resolution,[],[f25,f64])).
% 0.23/0.55  fof(f64,plain,(
% 0.23/0.55    r1_xboole_0(sK2,sK0) | ~spl3_5),
% 0.23/0.55    inference(avatar_component_clause,[],[f62])).
% 0.23/0.55  fof(f101,plain,(
% 0.23/0.55    spl3_8 | ~spl3_1),
% 0.23/0.55    inference(avatar_split_clause,[],[f83,f32,f91])).
% 0.23/0.55  fof(f32,plain,(
% 0.23/0.55    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.55  fof(f83,plain,(
% 0.23/0.55    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.23/0.55    inference(resolution,[],[f25,f34])).
% 0.23/0.55  fof(f34,plain,(
% 0.23/0.55    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.23/0.55    inference(avatar_component_clause,[],[f32])).
% 0.23/0.55  fof(f100,plain,(
% 0.23/0.55    spl3_9 | ~spl3_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f82,f37,f96])).
% 0.23/0.55  fof(f82,plain,(
% 0.23/0.55    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_2),
% 0.23/0.55    inference(resolution,[],[f25,f39])).
% 0.23/0.55  fof(f71,plain,(
% 0.23/0.55    spl3_5 | ~spl3_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f52,f37,f62])).
% 0.23/0.55  fof(f52,plain,(
% 0.23/0.55    r1_xboole_0(sK2,sK0) | ~spl3_2),
% 0.23/0.55    inference(resolution,[],[f22,f39])).
% 0.23/0.55  fof(f45,plain,(
% 0.23/0.55    ~spl3_3),
% 0.23/0.55    inference(avatar_split_clause,[],[f16,f42])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ~r1_xboole_0(sK0,sK1)),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  fof(f13,plain,(
% 0.23/0.55    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.23/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 0.23/0.55  fof(f12,plain,(
% 0.23/0.55    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.23/0.55    introduced(choice_axiom,[])).
% 0.23/0.55  fof(f10,plain,(
% 0.23/0.55    ? [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.23/0.55    inference(ennf_transformation,[],[f9])).
% 0.23/0.55  fof(f9,negated_conjecture,(
% 0.23/0.55    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.23/0.55    inference(negated_conjecture,[],[f8])).
% 0.23/0.55  fof(f8,conjecture,(
% 0.23/0.55    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).
% 0.23/0.55  fof(f40,plain,(
% 0.23/0.55    spl3_2),
% 0.23/0.55    inference(avatar_split_clause,[],[f17,f37])).
% 0.23/0.55  fof(f17,plain,(
% 0.23/0.55    r1_xboole_0(sK0,sK2)),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  fof(f35,plain,(
% 0.23/0.55    spl3_1),
% 0.23/0.55    inference(avatar_split_clause,[],[f18,f32])).
% 0.23/0.55  fof(f18,plain,(
% 0.23/0.55    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.23/0.55    inference(cnf_transformation,[],[f13])).
% 0.23/0.55  % SZS output end Proof for theBenchmark
% 0.23/0.55  % (1790)------------------------------
% 0.23/0.55  % (1790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (1790)Termination reason: Refutation
% 0.23/0.55  
% 0.23/0.55  % (1790)Memory used [KB]: 7036
% 0.23/0.55  % (1790)Time elapsed: 0.107 s
% 0.23/0.55  % (1790)------------------------------
% 0.23/0.55  % (1790)------------------------------
% 1.46/0.55  % (1783)Success in time 0.181 s
%------------------------------------------------------------------------------
