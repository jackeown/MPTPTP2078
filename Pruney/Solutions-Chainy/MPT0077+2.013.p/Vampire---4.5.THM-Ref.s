%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 1.69s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 214 expanded)
%              Number of leaves         :   25 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  250 ( 468 expanded)
%              Number of equality atoms :   53 ( 106 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f86,f160,f162,f175,f196,f223,f286,f291,f393,f1421,f1430,f1464,f1486])).

fof(f1486,plain,
    ( spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1485])).

fof(f1485,plain,
    ( $false
    | spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f174,f1482])).

fof(f1482,plain,
    ( r1_xboole_0(sK0,sK2)
    | spl5_2 ),
    inference(subsumption_resolution,[],[f38,f68])).

fof(f68,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f38,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f174,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_5
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1464,plain,
    ( spl5_15
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(avatar_contradiction_clause,[],[f1463])).

fof(f1463,plain,
    ( $false
    | spl5_15
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f1462,f387])).

fof(f387,plain,(
    ! [X4] : r1_tarski(X4,X4) ),
    inference(superposition,[],[f42,f95])).

fof(f95,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f91,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f91,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1462,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_15
    | ~ spl5_24
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f1454,f1429])).

fof(f1429,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f1427,plain,
    ( spl5_26
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f1454,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,sK2))
    | spl5_15
    | ~ spl5_24 ),
    inference(backward_demodulation,[],[f395,f1436])).

fof(f1436,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl5_24 ),
    inference(superposition,[],[f55,f1420])).

fof(f1420,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1418,plain,
    ( spl5_24
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f395,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_15 ),
    inference(unit_resulting_resolution,[],[f392,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f392,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl5_15
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f1430,plain,
    ( spl5_26
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f663,f288,f1427])).

fof(f288,plain,
    ( spl5_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f663,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f662,f567])).

fof(f567,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f137,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f137,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f57,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f662,plain,
    ( k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f661,f40])).

fof(f661,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f625,f40])).

fof(f625,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),sK0),k1_xboole_0)
    | ~ spl5_12 ),
    inference(superposition,[],[f90,f290])).

fof(f290,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f288])).

fof(f90,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4)) ),
    inference(superposition,[],[f46,f45])).

fof(f1421,plain,
    ( spl5_24
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f651,f283,f1418])).

fof(f283,plain,
    ( spl5_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f651,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f650,f567])).

fof(f650,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f649,f40])).

fof(f649,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f624,f40])).

fof(f624,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),k1_xboole_0)
    | ~ spl5_11 ),
    inference(superposition,[],[f90,f285])).

fof(f285,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f283])).

fof(f393,plain,
    ( ~ spl5_15
    | spl5_2 ),
    inference(avatar_split_clause,[],[f239,f67,f390])).

fof(f239,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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

fof(f291,plain,
    ( spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f231,f172,f288])).

fof(f231,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f173,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f51,f44])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f173,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f172])).

fof(f286,plain,
    ( spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f164,f63,f283])).

fof(f63,plain,
    ( spl5_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f164,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f65,f61])).

fof(f65,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f223,plain,
    ( ~ spl5_4
    | spl5_7 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_4
    | spl5_7 ),
    inference(subsumption_resolution,[],[f216,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f42,f43])).

fof(f216,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl5_4
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f195,f159,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f159,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_4
  <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f195,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl5_7
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f196,plain,
    ( ~ spl5_7
    | spl5_5 ),
    inference(avatar_split_clause,[],[f179,f172,f193])).

fof(f179,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f174,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f175,plain,
    ( ~ spl5_1
    | ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f163,f67,f172,f63])).

fof(f163,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f33,f69])).

fof(f69,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f162,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f159,f106])).

fof(f106,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK1,X0),sK0)
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f42,f85,f56])).

fof(f85,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_3
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f160,plain,
    ( spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f72,f67,f157])).

fof(f72,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f69,f50])).

fof(f86,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f71,f63,f83])).

fof(f71,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f64,f50])).

fof(f64,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f70,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f37,f67,f63])).

fof(f37,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (31519)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (31528)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (31517)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (31523)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.50  % (31526)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (31520)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (31516)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.50  % (31524)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (31518)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.51  % (31525)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.51  % (31513)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.52  % (31529)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (31522)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.53  % (31530)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.49/0.56  % (31514)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.49/0.57  % (31515)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.69/0.57  % (31521)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.69/0.58  % (31527)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.69/0.59  % (31528)Refutation found. Thanks to Tanya!
% 1.69/0.59  % SZS status Theorem for theBenchmark
% 1.69/0.59  % SZS output start Proof for theBenchmark
% 1.69/0.59  fof(f1487,plain,(
% 1.69/0.59    $false),
% 1.69/0.59    inference(avatar_sat_refutation,[],[f70,f86,f160,f162,f175,f196,f223,f286,f291,f393,f1421,f1430,f1464,f1486])).
% 1.69/0.59  fof(f1486,plain,(
% 1.69/0.59    spl5_2 | spl5_5),
% 1.69/0.59    inference(avatar_contradiction_clause,[],[f1485])).
% 1.69/0.59  fof(f1485,plain,(
% 1.69/0.59    $false | (spl5_2 | spl5_5)),
% 1.69/0.59    inference(subsumption_resolution,[],[f174,f1482])).
% 1.69/0.59  fof(f1482,plain,(
% 1.69/0.59    r1_xboole_0(sK0,sK2) | spl5_2),
% 1.69/0.59    inference(subsumption_resolution,[],[f38,f68])).
% 1.69/0.59  fof(f68,plain,(
% 1.69/0.59    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl5_2),
% 1.69/0.59    inference(avatar_component_clause,[],[f67])).
% 1.69/0.59  fof(f67,plain,(
% 1.69/0.59    spl5_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.69/0.59  fof(f38,plain,(
% 1.69/0.59    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 1.69/0.59    inference(cnf_transformation,[],[f26])).
% 1.69/0.59  fof(f26,plain,(
% 1.69/0.59    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.69/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f25])).
% 1.69/0.59  fof(f25,plain,(
% 1.69/0.59    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 1.69/0.59    introduced(choice_axiom,[])).
% 1.69/0.59  fof(f19,plain,(
% 1.69/0.59    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.69/0.59    inference(ennf_transformation,[],[f17])).
% 1.69/0.59  fof(f17,negated_conjecture,(
% 1.69/0.59    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.69/0.59    inference(negated_conjecture,[],[f16])).
% 1.69/0.59  fof(f16,conjecture,(
% 1.69/0.59    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.69/0.59  fof(f174,plain,(
% 1.69/0.59    ~r1_xboole_0(sK0,sK2) | spl5_5),
% 1.69/0.59    inference(avatar_component_clause,[],[f172])).
% 1.69/0.59  fof(f172,plain,(
% 1.69/0.59    spl5_5 <=> r1_xboole_0(sK0,sK2)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.69/0.59  fof(f1464,plain,(
% 1.69/0.59    spl5_15 | ~spl5_24 | ~spl5_26),
% 1.69/0.59    inference(avatar_contradiction_clause,[],[f1463])).
% 1.69/0.59  fof(f1463,plain,(
% 1.69/0.59    $false | (spl5_15 | ~spl5_24 | ~spl5_26)),
% 1.69/0.59    inference(subsumption_resolution,[],[f1462,f387])).
% 1.69/0.59  fof(f387,plain,(
% 1.69/0.59    ( ! [X4] : (r1_tarski(X4,X4)) )),
% 1.69/0.59    inference(superposition,[],[f42,f95])).
% 1.69/0.59  fof(f95,plain,(
% 1.69/0.59    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.69/0.59    inference(forward_demodulation,[],[f91,f40])).
% 1.69/0.59  fof(f40,plain,(
% 1.69/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f9])).
% 1.69/0.59  fof(f9,axiom,(
% 1.69/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.69/0.59  fof(f91,plain,(
% 1.69/0.59    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) )),
% 1.69/0.59    inference(superposition,[],[f46,f40])).
% 1.69/0.59  fof(f46,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f10])).
% 1.69/0.59  fof(f10,axiom,(
% 1.69/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.69/0.59  fof(f42,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f15])).
% 1.69/0.59  fof(f15,axiom,(
% 1.69/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.69/0.59  fof(f1462,plain,(
% 1.69/0.59    ~r1_tarski(sK0,sK0) | (spl5_15 | ~spl5_24 | ~spl5_26)),
% 1.69/0.59    inference(forward_demodulation,[],[f1454,f1429])).
% 1.69/0.59  fof(f1429,plain,(
% 1.69/0.59    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_26),
% 1.69/0.59    inference(avatar_component_clause,[],[f1427])).
% 1.69/0.59  fof(f1427,plain,(
% 1.69/0.59    spl5_26 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.69/0.59  fof(f1454,plain,(
% 1.69/0.59    ~r1_tarski(sK0,k4_xboole_0(sK0,sK2)) | (spl5_15 | ~spl5_24)),
% 1.69/0.59    inference(backward_demodulation,[],[f395,f1436])).
% 1.69/0.59  fof(f1436,plain,(
% 1.69/0.59    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | ~spl5_24),
% 1.69/0.59    inference(superposition,[],[f55,f1420])).
% 1.69/0.59  fof(f1420,plain,(
% 1.69/0.59    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_24),
% 1.69/0.59    inference(avatar_component_clause,[],[f1418])).
% 1.69/0.59  fof(f1418,plain,(
% 1.69/0.59    spl5_24 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.69/0.59  fof(f55,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f11])).
% 1.69/0.59  fof(f11,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.69/0.59  fof(f395,plain,(
% 1.69/0.59    ~r1_tarski(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl5_15),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f392,f54])).
% 1.69/0.59  fof(f54,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f32])).
% 1.69/0.59  fof(f32,plain,(
% 1.69/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.69/0.59    inference(nnf_transformation,[],[f6])).
% 1.69/0.59  fof(f6,axiom,(
% 1.69/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.69/0.59  fof(f392,plain,(
% 1.69/0.59    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl5_15),
% 1.69/0.59    inference(avatar_component_clause,[],[f390])).
% 1.69/0.59  fof(f390,plain,(
% 1.69/0.59    spl5_15 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.69/0.59  fof(f1430,plain,(
% 1.69/0.59    spl5_26 | ~spl5_12),
% 1.69/0.59    inference(avatar_split_clause,[],[f663,f288,f1427])).
% 1.69/0.59  fof(f288,plain,(
% 1.69/0.59    spl5_12 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.69/0.59  fof(f663,plain,(
% 1.69/0.59    sK0 = k4_xboole_0(sK0,sK2) | ~spl5_12),
% 1.69/0.59    inference(forward_demodulation,[],[f662,f567])).
% 1.69/0.59  fof(f567,plain,(
% 1.69/0.59    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.69/0.59    inference(superposition,[],[f137,f45])).
% 1.69/0.59  fof(f45,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f8])).
% 1.69/0.59  fof(f8,axiom,(
% 1.69/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.69/0.59  fof(f137,plain,(
% 1.69/0.59    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 1.69/0.59    inference(superposition,[],[f57,f43])).
% 1.69/0.59  fof(f43,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f1])).
% 1.69/0.59  fof(f1,axiom,(
% 1.69/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.69/0.59  fof(f57,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.69/0.59    inference(definition_unfolding,[],[f47,f44])).
% 1.69/0.59  fof(f44,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f12])).
% 1.69/0.59  fof(f12,axiom,(
% 1.69/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.69/0.59  fof(f47,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f13])).
% 1.69/0.59  fof(f13,axiom,(
% 1.69/0.59    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.69/0.59  fof(f662,plain,(
% 1.69/0.59    k4_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) | ~spl5_12),
% 1.69/0.59    inference(forward_demodulation,[],[f661,f40])).
% 1.69/0.59  fof(f661,plain,(
% 1.69/0.59    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) | ~spl5_12),
% 1.69/0.59    inference(forward_demodulation,[],[f625,f40])).
% 1.69/0.59  fof(f625,plain,(
% 1.69/0.59    k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK2),sK0),k1_xboole_0) | ~spl5_12),
% 1.69/0.59    inference(superposition,[],[f90,f290])).
% 1.69/0.59  fof(f290,plain,(
% 1.69/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_12),
% 1.69/0.59    inference(avatar_component_clause,[],[f288])).
% 1.69/0.59  fof(f90,plain,(
% 1.69/0.59    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) )),
% 1.69/0.59    inference(superposition,[],[f46,f45])).
% 1.69/0.59  fof(f1421,plain,(
% 1.69/0.59    spl5_24 | ~spl5_11),
% 1.69/0.59    inference(avatar_split_clause,[],[f651,f283,f1418])).
% 1.69/0.59  fof(f283,plain,(
% 1.69/0.59    spl5_11 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.69/0.59  fof(f651,plain,(
% 1.69/0.59    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_11),
% 1.69/0.59    inference(forward_demodulation,[],[f650,f567])).
% 1.69/0.59  fof(f650,plain,(
% 1.69/0.59    k4_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl5_11),
% 1.69/0.59    inference(forward_demodulation,[],[f649,f40])).
% 1.69/0.59  fof(f649,plain,(
% 1.69/0.59    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl5_11),
% 1.69/0.59    inference(forward_demodulation,[],[f624,f40])).
% 1.69/0.59  fof(f624,plain,(
% 1.69/0.59    k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),sK0),k1_xboole_0) | ~spl5_11),
% 1.69/0.59    inference(superposition,[],[f90,f285])).
% 1.69/0.59  fof(f285,plain,(
% 1.69/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_11),
% 1.69/0.59    inference(avatar_component_clause,[],[f283])).
% 1.69/0.59  fof(f393,plain,(
% 1.69/0.59    ~spl5_15 | spl5_2),
% 1.69/0.59    inference(avatar_split_clause,[],[f239,f67,f390])).
% 1.69/0.59  fof(f239,plain,(
% 1.69/0.59    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) | spl5_2),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f68,f60])).
% 1.69/0.59  fof(f60,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.69/0.59    inference(definition_unfolding,[],[f52,f44])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f31])).
% 1.69/0.59  fof(f31,plain,(
% 1.69/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.69/0.59    inference(nnf_transformation,[],[f2])).
% 1.69/0.59  fof(f2,axiom,(
% 1.69/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.69/0.59  fof(f291,plain,(
% 1.69/0.59    spl5_12 | ~spl5_5),
% 1.69/0.59    inference(avatar_split_clause,[],[f231,f172,f288])).
% 1.69/0.59  fof(f231,plain,(
% 1.69/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl5_5),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f173,f61])).
% 1.69/0.59  fof(f61,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.69/0.59    inference(definition_unfolding,[],[f51,f44])).
% 1.69/0.59  fof(f51,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f31])).
% 1.69/0.59  fof(f173,plain,(
% 1.69/0.59    r1_xboole_0(sK0,sK2) | ~spl5_5),
% 1.69/0.59    inference(avatar_component_clause,[],[f172])).
% 1.69/0.59  fof(f286,plain,(
% 1.69/0.59    spl5_11 | ~spl5_1),
% 1.69/0.59    inference(avatar_split_clause,[],[f164,f63,f283])).
% 1.69/0.59  fof(f63,plain,(
% 1.69/0.59    spl5_1 <=> r1_xboole_0(sK0,sK1)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.69/0.59  fof(f164,plain,(
% 1.69/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_1),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f65,f61])).
% 1.69/0.59  fof(f65,plain,(
% 1.69/0.59    r1_xboole_0(sK0,sK1) | ~spl5_1),
% 1.69/0.59    inference(avatar_component_clause,[],[f63])).
% 1.69/0.59  fof(f223,plain,(
% 1.69/0.59    ~spl5_4 | spl5_7),
% 1.69/0.59    inference(avatar_contradiction_clause,[],[f222])).
% 1.69/0.59  fof(f222,plain,(
% 1.69/0.59    $false | (~spl5_4 | spl5_7)),
% 1.69/0.59    inference(subsumption_resolution,[],[f216,f74])).
% 1.69/0.59  fof(f74,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.69/0.59    inference(superposition,[],[f42,f43])).
% 1.69/0.59  fof(f216,plain,(
% 1.69/0.59    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl5_4 | spl5_7)),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f195,f159,f56])).
% 1.69/0.59  fof(f56,plain,(
% 1.69/0.59    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f24])).
% 1.69/0.59  fof(f24,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.69/0.59    inference(flattening,[],[f23])).
% 1.69/0.59  fof(f23,plain,(
% 1.69/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.69/0.59    inference(ennf_transformation,[],[f14])).
% 1.69/0.59  fof(f14,axiom,(
% 1.69/0.59    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.69/0.59  fof(f159,plain,(
% 1.69/0.59    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl5_4),
% 1.69/0.59    inference(avatar_component_clause,[],[f157])).
% 1.69/0.59  fof(f157,plain,(
% 1.69/0.59    spl5_4 <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.69/0.59  fof(f195,plain,(
% 1.69/0.59    ~r1_xboole_0(sK2,sK0) | spl5_7),
% 1.69/0.59    inference(avatar_component_clause,[],[f193])).
% 1.69/0.59  fof(f193,plain,(
% 1.69/0.59    spl5_7 <=> r1_xboole_0(sK2,sK0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.69/0.59  fof(f196,plain,(
% 1.69/0.59    ~spl5_7 | spl5_5),
% 1.69/0.59    inference(avatar_split_clause,[],[f179,f172,f193])).
% 1.69/0.59  fof(f179,plain,(
% 1.69/0.59    ~r1_xboole_0(sK2,sK0) | spl5_5),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f174,f50])).
% 1.69/0.59  fof(f50,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f22])).
% 1.69/0.59  fof(f22,plain,(
% 1.69/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f3])).
% 1.69/0.59  fof(f3,axiom,(
% 1.69/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.69/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.69/0.59  fof(f175,plain,(
% 1.69/0.59    ~spl5_1 | ~spl5_5 | ~spl5_2),
% 1.69/0.59    inference(avatar_split_clause,[],[f163,f67,f172,f63])).
% 1.69/0.59  fof(f163,plain,(
% 1.69/0.59    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~spl5_2),
% 1.69/0.59    inference(subsumption_resolution,[],[f33,f69])).
% 1.69/0.59  fof(f69,plain,(
% 1.69/0.59    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl5_2),
% 1.69/0.59    inference(avatar_component_clause,[],[f67])).
% 1.69/0.59  fof(f33,plain,(
% 1.69/0.59    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.69/0.59    inference(cnf_transformation,[],[f26])).
% 1.69/0.59  fof(f162,plain,(
% 1.69/0.59    spl5_3 | ~spl5_4),
% 1.69/0.59    inference(avatar_contradiction_clause,[],[f161])).
% 1.69/0.59  fof(f161,plain,(
% 1.69/0.59    $false | (spl5_3 | ~spl5_4)),
% 1.69/0.59    inference(subsumption_resolution,[],[f159,f106])).
% 1.69/0.59  fof(f106,plain,(
% 1.69/0.59    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK1,X0),sK0)) ) | spl5_3),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f42,f85,f56])).
% 1.69/0.59  fof(f85,plain,(
% 1.69/0.59    ~r1_xboole_0(sK1,sK0) | spl5_3),
% 1.69/0.59    inference(avatar_component_clause,[],[f83])).
% 1.69/0.59  fof(f83,plain,(
% 1.69/0.59    spl5_3 <=> r1_xboole_0(sK1,sK0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.69/0.59  fof(f160,plain,(
% 1.69/0.59    spl5_4 | ~spl5_2),
% 1.69/0.59    inference(avatar_split_clause,[],[f72,f67,f157])).
% 1.69/0.59  fof(f72,plain,(
% 1.69/0.59    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl5_2),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f69,f50])).
% 1.69/0.59  fof(f86,plain,(
% 1.69/0.59    ~spl5_3 | spl5_1),
% 1.69/0.59    inference(avatar_split_clause,[],[f71,f63,f83])).
% 1.69/0.59  fof(f71,plain,(
% 1.69/0.59    ~r1_xboole_0(sK1,sK0) | spl5_1),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f64,f50])).
% 1.69/0.59  fof(f64,plain,(
% 1.69/0.59    ~r1_xboole_0(sK0,sK1) | spl5_1),
% 1.69/0.59    inference(avatar_component_clause,[],[f63])).
% 1.69/0.59  fof(f70,plain,(
% 1.69/0.59    spl5_1 | spl5_2),
% 1.69/0.59    inference(avatar_split_clause,[],[f37,f67,f63])).
% 1.69/0.59  fof(f37,plain,(
% 1.69/0.59    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 1.69/0.59    inference(cnf_transformation,[],[f26])).
% 1.69/0.59  % SZS output end Proof for theBenchmark
% 1.69/0.59  % (31528)------------------------------
% 1.69/0.59  % (31528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (31528)Termination reason: Refutation
% 1.69/0.59  
% 1.69/0.59  % (31528)Memory used [KB]: 12025
% 1.69/0.59  % (31528)Time elapsed: 0.103 s
% 1.69/0.59  % (31528)------------------------------
% 1.69/0.59  % (31528)------------------------------
% 1.69/0.60  % (31512)Success in time 0.235 s
%------------------------------------------------------------------------------
