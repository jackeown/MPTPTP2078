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
% DateTime   : Thu Dec  3 12:33:01 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 324 expanded)
%              Number of leaves         :   39 ( 159 expanded)
%              Depth                    :   10
%              Number of atoms          :  377 ( 695 expanded)
%              Number of equality atoms :  121 ( 288 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1829,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f59,f69,f75,f81,f85,f91,f96,f107,f128,f153,f161,f176,f193,f272,f342,f503,f520,f1661,f1701,f1727,f1771,f1787,f1799,f1827])).

fof(f1827,plain,
    ( ~ spl3_44
    | ~ spl3_101
    | spl3_103
    | ~ spl3_105 ),
    inference(avatar_contradiction_clause,[],[f1826])).

fof(f1826,plain,
    ( $false
    | ~ spl3_44
    | ~ spl3_101
    | spl3_103
    | ~ spl3_105 ),
    inference(subsumption_resolution,[],[f1786,f1825])).

fof(f1825,plain,
    ( ! [X9] : k2_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,sK1)),k3_xboole_0(X9,k5_xboole_0(sK1,sK2))) = k5_xboole_0(X9,k3_xboole_0(X9,sK2))
    | ~ spl3_44
    | ~ spl3_101
    | ~ spl3_105 ),
    inference(forward_demodulation,[],[f1814,f1770])).

fof(f1770,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_101 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f1768,plain,
    ( spl3_101
  <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).

fof(f1814,plain,
    ( ! [X9] : k2_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,sK1)),k3_xboole_0(X9,k5_xboole_0(sK1,sK2))) = k5_xboole_0(X9,k3_xboole_0(X9,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))
    | ~ spl3_44
    | ~ spl3_105 ),
    inference(superposition,[],[f502,f1798])).

fof(f1798,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_105 ),
    inference(avatar_component_clause,[],[f1796])).

fof(f1796,plain,
    ( spl3_105
  <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).

fof(f502,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f1786,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | spl3_103 ),
    inference(avatar_component_clause,[],[f1784])).

fof(f1784,plain,
    ( spl3_103
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f1799,plain,
    ( spl3_105
    | ~ spl3_46
    | ~ spl3_98 ),
    inference(avatar_split_clause,[],[f1743,f1724,f518,f1796])).

fof(f518,plain,
    ( spl3_46
  <=> ! [X3,X4] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k3_xboole_0(X3,k5_xboole_0(X3,k3_xboole_0(X3,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1724,plain,
    ( spl3_98
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).

fof(f1743,plain,
    ( k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_46
    | ~ spl3_98 ),
    inference(superposition,[],[f519,f1726])).

fof(f1726,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_98 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f519,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k3_xboole_0(X3,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f518])).

fof(f1787,plain,
    ( ~ spl3_103
    | ~ spl3_19
    | ~ spl3_21
    | spl3_23
    | ~ spl3_97 ),
    inference(avatar_split_clause,[],[f1713,f1699,f190,f173,f158,f1784])).

fof(f158,plain,
    ( spl3_19
  <=> k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f173,plain,
    ( spl3_21
  <=> k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f190,plain,
    ( spl3_23
  <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f1699,plain,
    ( spl3_97
  <=> ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).

fof(f1713,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))
    | ~ spl3_19
    | ~ spl3_21
    | spl3_23
    | ~ spl3_97 ),
    inference(backward_demodulation,[],[f192,f1711])).

fof(f1711,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_97 ),
    inference(backward_demodulation,[],[f175,f1704])).

fof(f1704,plain,
    ( sK2 = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2)
    | ~ spl3_19
    | ~ spl3_97 ),
    inference(superposition,[],[f1700,f160])).

fof(f160,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1700,plain,
    ( ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0
    | ~ spl3_97 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f175,plain,
    ( k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f173])).

fof(f192,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f190])).

fof(f1771,plain,
    ( spl3_101
    | ~ spl3_33
    | ~ spl3_98 ),
    inference(avatar_split_clause,[],[f1741,f1724,f340,f1768])).

fof(f340,plain,
    ( spl3_33
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1741,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ spl3_33
    | ~ spl3_98 ),
    inference(superposition,[],[f341,f1726])).

fof(f341,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f340])).

fof(f1727,plain,
    ( spl3_98
    | ~ spl3_19
    | ~ spl3_21
    | ~ spl3_97 ),
    inference(avatar_split_clause,[],[f1711,f1699,f173,f158,f1724])).

fof(f1701,plain,
    ( spl3_97
    | ~ spl3_5
    | ~ spl3_96 ),
    inference(avatar_split_clause,[],[f1665,f1659,f57,f1699])).

fof(f57,plain,
    ( spl3_5
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1659,plain,
    ( spl3_96
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f1665,plain,
    ( ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0
    | ~ spl3_5
    | ~ spl3_96 ),
    inference(superposition,[],[f1660,f58])).

fof(f58,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f1660,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X1))
    | ~ spl3_96 ),
    inference(avatar_component_clause,[],[f1659])).

fof(f1661,plain,
    ( spl3_96
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_33
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f748,f518,f501,f340,f105,f57,f1659])).

fof(f105,plain,
    ( spl3_13
  <=> ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f748,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X1))
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_33
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f747,f106])).

fof(f106,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f747,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X1))
    | ~ spl3_5
    | ~ spl3_33
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f746,f58])).

fof(f746,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k3_xboole_0(X0,X1))
    | ~ spl3_33
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f702,f341])).

fof(f702,plain,
    ( ! [X0,X1] : k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(superposition,[],[f502,f519])).

fof(f520,plain,
    ( spl3_46
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f274,f270,f57,f518])).

fof(f270,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f274,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k3_xboole_0(X3,k5_xboole_0(X3,k3_xboole_0(X3,X4)))
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(superposition,[],[f271,f58])).

fof(f271,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f270])).

fof(f503,plain,(
    spl3_44 ),
    inference(avatar_split_clause,[],[f37,f501])).

fof(f37,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(definition_unfolding,[],[f30,f25,f25,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f342,plain,
    ( spl3_33
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f296,f270,f94,f57,f340])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f296,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f95,f274])).

fof(f95,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f272,plain,(
    spl3_31 ),
    inference(avatar_split_clause,[],[f36,f270])).

fof(f36,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f29,f25,f25])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f193,plain,(
    ~ spl3_23 ),
    inference(avatar_split_clause,[],[f32,f190])).

fof(f32,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f20,f25,f25,f25])).

fof(f20,plain,(
    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
        & r1_tarski(X2,X1) )
   => ( k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2)))
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).

fof(f176,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f156,f150,f126,f105,f94,f88,f78,f57,f173])).

fof(f78,plain,
    ( spl3_9
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f88,plain,
    ( spl3_11
  <=> sK1 = k2_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f126,plain,
    ( spl3_16
  <=> ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f150,plain,
    ( spl3_18
  <=> k5_xboole_0(sK2,sK2) = k3_xboole_0(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f156,plain,
    ( k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f141,f154])).

fof(f154,plain,
    ( k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(superposition,[],[f152,f106])).

fof(f152,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f150])).

fof(f141,plain,
    ( k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK2,k1_xboole_0),sK2)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f140,f95])).

fof(f140,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k3_xboole_0(sK2,k1_xboole_0),sK2)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f139,f106])).

fof(f139,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK2,sK2),sK2)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f138,f80])).

fof(f80,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f138,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),sK2)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f137,f58])).

fof(f137,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK2))
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f130,f37])).

fof(f130,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(superposition,[],[f127,f90])).

fof(f90,plain,
    ( sK1 = k2_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f88])).

fof(f127,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f161,plain,
    ( spl3_19
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f154,f150,f105,f158])).

fof(f153,plain,
    ( spl3_18
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f136,f126,f105,f78,f72,f57,f150])).

fof(f72,plain,
    ( spl3_8
  <=> sK1 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f136,plain,
    ( k5_xboole_0(sK2,sK2) = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f135,f80])).

fof(f135,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f134,f106])).

fof(f134,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,sK1)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f129,f58])).

fof(f129,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(superposition,[],[f127,f74])).

fof(f74,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f128,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f34,f126])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1)) ),
    inference(definition_unfolding,[],[f26,f25,f25])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f107,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f102,f94,f57,f52,f105])).

fof(f52,plain,
    ( spl3_4
  <=> ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f102,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f100,f58])).

fof(f100,plain,
    ( ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f95,f53])).

fof(f53,plain,
    ( ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f31,f94])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f24,f25,f25])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f91,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f86,f83,f39,f88])).

fof(f39,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f83,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f86,plain,
    ( sK1 = k2_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(resolution,[],[f84,f41])).

fof(f41,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f35,f83])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f81,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f76,f72,f48,f78])).

fof(f48,plain,
    ( spl3_3
  <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(superposition,[],[f49,f74])).

fof(f49,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f75,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f70,f67,f39,f72])).

fof(f67,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f70,plain,
    ( sK1 = k2_xboole_0(sK2,sK1)
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f68,f41])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f59,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f48,f44,f57])).

fof(f44,plain,
    ( spl3_2
  <=> ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f55,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,
    ( ! [X0] : k2_xboole_0(X0,X0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f33,f52])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f50,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f46,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f42,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:23:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (16778)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.46  % (16765)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (16764)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (16774)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (16762)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (16771)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (16770)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (16763)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (16777)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (16772)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (16768)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (16775)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.50  % (16761)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (16766)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (16769)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (16767)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (16773)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.26/0.52  % (16776)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.43/0.57  % (16768)Refutation found. Thanks to Tanya!
% 1.43/0.57  % SZS status Theorem for theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f1829,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(avatar_sat_refutation,[],[f42,f46,f50,f54,f59,f69,f75,f81,f85,f91,f96,f107,f128,f153,f161,f176,f193,f272,f342,f503,f520,f1661,f1701,f1727,f1771,f1787,f1799,f1827])).
% 1.43/0.57  fof(f1827,plain,(
% 1.43/0.57    ~spl3_44 | ~spl3_101 | spl3_103 | ~spl3_105),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f1826])).
% 1.43/0.57  fof(f1826,plain,(
% 1.43/0.57    $false | (~spl3_44 | ~spl3_101 | spl3_103 | ~spl3_105)),
% 1.43/0.57    inference(subsumption_resolution,[],[f1786,f1825])).
% 1.43/0.57  fof(f1825,plain,(
% 1.43/0.57    ( ! [X9] : (k2_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,sK1)),k3_xboole_0(X9,k5_xboole_0(sK1,sK2))) = k5_xboole_0(X9,k3_xboole_0(X9,sK2))) ) | (~spl3_44 | ~spl3_101 | ~spl3_105)),
% 1.43/0.57    inference(forward_demodulation,[],[f1814,f1770])).
% 1.43/0.57  fof(f1770,plain,(
% 1.43/0.57    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_101),
% 1.43/0.57    inference(avatar_component_clause,[],[f1768])).
% 1.43/0.57  fof(f1768,plain,(
% 1.43/0.57    spl3_101 <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_101])])).
% 1.43/0.57  fof(f1814,plain,(
% 1.43/0.57    ( ! [X9] : (k2_xboole_0(k5_xboole_0(X9,k3_xboole_0(X9,sK1)),k3_xboole_0(X9,k5_xboole_0(sK1,sK2))) = k5_xboole_0(X9,k3_xboole_0(X9,k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))))) ) | (~spl3_44 | ~spl3_105)),
% 1.43/0.57    inference(superposition,[],[f502,f1798])).
% 1.43/0.57  fof(f1798,plain,(
% 1.43/0.57    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~spl3_105),
% 1.43/0.57    inference(avatar_component_clause,[],[f1796])).
% 1.43/0.57  fof(f1796,plain,(
% 1.43/0.57    spl3_105 <=> k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_105])])).
% 1.43/0.57  fof(f502,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))) ) | ~spl3_44),
% 1.43/0.57    inference(avatar_component_clause,[],[f501])).
% 1.43/0.57  fof(f501,plain,(
% 1.43/0.57    spl3_44 <=> ! [X1,X0,X2] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.43/0.57  fof(f1786,plain,(
% 1.43/0.57    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | spl3_103),
% 1.43/0.57    inference(avatar_component_clause,[],[f1784])).
% 1.43/0.57  fof(f1784,plain,(
% 1.43/0.57    spl3_103 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 1.43/0.57  fof(f1799,plain,(
% 1.43/0.57    spl3_105 | ~spl3_46 | ~spl3_98),
% 1.43/0.57    inference(avatar_split_clause,[],[f1743,f1724,f518,f1796])).
% 1.43/0.57  fof(f518,plain,(
% 1.43/0.57    spl3_46 <=> ! [X3,X4] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k3_xboole_0(X3,k5_xboole_0(X3,k3_xboole_0(X3,X4)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.43/0.57  fof(f1724,plain,(
% 1.43/0.57    spl3_98 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_98])])).
% 1.43/0.57  fof(f1743,plain,(
% 1.43/0.57    k5_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | (~spl3_46 | ~spl3_98)),
% 1.43/0.57    inference(superposition,[],[f519,f1726])).
% 1.43/0.57  fof(f1726,plain,(
% 1.43/0.57    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_98),
% 1.43/0.57    inference(avatar_component_clause,[],[f1724])).
% 1.43/0.57  fof(f519,plain,(
% 1.43/0.57    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k3_xboole_0(X3,k5_xboole_0(X3,k3_xboole_0(X3,X4)))) ) | ~spl3_46),
% 1.43/0.57    inference(avatar_component_clause,[],[f518])).
% 1.43/0.57  fof(f1787,plain,(
% 1.43/0.57    ~spl3_103 | ~spl3_19 | ~spl3_21 | spl3_23 | ~spl3_97),
% 1.43/0.57    inference(avatar_split_clause,[],[f1713,f1699,f190,f173,f158,f1784])).
% 1.43/0.57  fof(f158,plain,(
% 1.43/0.57    spl3_19 <=> k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.43/0.57  fof(f173,plain,(
% 1.43/0.57    spl3_21 <=> k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.43/0.57  fof(f190,plain,(
% 1.43/0.57    spl3_23 <=> k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.43/0.57  fof(f1699,plain,(
% 1.43/0.57    spl3_97 <=> ! [X0] : k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_97])])).
% 1.43/0.57  fof(f1713,plain,(
% 1.43/0.57    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,sK2))) | (~spl3_19 | ~spl3_21 | spl3_23 | ~spl3_97)),
% 1.43/0.57    inference(backward_demodulation,[],[f192,f1711])).
% 1.43/0.57  fof(f1711,plain,(
% 1.43/0.57    sK2 = k3_xboole_0(sK1,sK2) | (~spl3_19 | ~spl3_21 | ~spl3_97)),
% 1.43/0.57    inference(backward_demodulation,[],[f175,f1704])).
% 1.43/0.57  fof(f1704,plain,(
% 1.43/0.57    sK2 = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2) | (~spl3_19 | ~spl3_97)),
% 1.43/0.57    inference(superposition,[],[f1700,f160])).
% 1.43/0.57  fof(f160,plain,(
% 1.43/0.57    k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) | ~spl3_19),
% 1.43/0.57    inference(avatar_component_clause,[],[f158])).
% 1.43/0.57  fof(f1700,plain,(
% 1.43/0.57    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0) ) | ~spl3_97),
% 1.43/0.57    inference(avatar_component_clause,[],[f1699])).
% 1.43/0.57  fof(f175,plain,(
% 1.43/0.57    k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2) | ~spl3_21),
% 1.43/0.57    inference(avatar_component_clause,[],[f173])).
% 1.43/0.57  fof(f192,plain,(
% 1.43/0.57    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | spl3_23),
% 1.43/0.57    inference(avatar_component_clause,[],[f190])).
% 1.43/0.57  fof(f1771,plain,(
% 1.43/0.57    spl3_101 | ~spl3_33 | ~spl3_98),
% 1.43/0.57    inference(avatar_split_clause,[],[f1741,f1724,f340,f1768])).
% 1.43/0.57  fof(f340,plain,(
% 1.43/0.57    spl3_33 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.43/0.57  fof(f1741,plain,(
% 1.43/0.57    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | (~spl3_33 | ~spl3_98)),
% 1.43/0.57    inference(superposition,[],[f341,f1726])).
% 1.43/0.57  fof(f341,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | ~spl3_33),
% 1.43/0.57    inference(avatar_component_clause,[],[f340])).
% 1.43/0.57  fof(f1727,plain,(
% 1.43/0.57    spl3_98 | ~spl3_19 | ~spl3_21 | ~spl3_97),
% 1.43/0.57    inference(avatar_split_clause,[],[f1711,f1699,f173,f158,f1724])).
% 1.43/0.57  fof(f1701,plain,(
% 1.43/0.57    spl3_97 | ~spl3_5 | ~spl3_96),
% 1.43/0.57    inference(avatar_split_clause,[],[f1665,f1659,f57,f1699])).
% 1.43/0.57  fof(f57,plain,(
% 1.43/0.57    spl3_5 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.43/0.57  fof(f1659,plain,(
% 1.43/0.57    spl3_96 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 1.43/0.57  fof(f1665,plain,(
% 1.43/0.57    ( ! [X0] : (k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),X0) = X0) ) | (~spl3_5 | ~spl3_96)),
% 1.43/0.57    inference(superposition,[],[f1660,f58])).
% 1.43/0.57  fof(f58,plain,(
% 1.43/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl3_5),
% 1.43/0.57    inference(avatar_component_clause,[],[f57])).
% 1.43/0.57  fof(f1660,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X1))) ) | ~spl3_96),
% 1.43/0.57    inference(avatar_component_clause,[],[f1659])).
% 1.43/0.57  fof(f1661,plain,(
% 1.43/0.57    spl3_96 | ~spl3_5 | ~spl3_13 | ~spl3_33 | ~spl3_44 | ~spl3_46),
% 1.43/0.57    inference(avatar_split_clause,[],[f748,f518,f501,f340,f105,f57,f1659])).
% 1.43/0.57  fof(f105,plain,(
% 1.43/0.57    spl3_13 <=> ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.43/0.57  fof(f748,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k3_xboole_0(X0,X1))) ) | (~spl3_5 | ~spl3_13 | ~spl3_33 | ~spl3_44 | ~spl3_46)),
% 1.43/0.57    inference(forward_demodulation,[],[f747,f106])).
% 1.43/0.57  fof(f106,plain,(
% 1.43/0.57    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) ) | ~spl3_13),
% 1.43/0.57    inference(avatar_component_clause,[],[f105])).
% 1.43/0.57  fof(f747,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X0),k3_xboole_0(X0,X1))) ) | (~spl3_5 | ~spl3_33 | ~spl3_44 | ~spl3_46)),
% 1.43/0.57    inference(forward_demodulation,[],[f746,f58])).
% 1.43/0.57  fof(f746,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k3_xboole_0(X0,X1))) ) | (~spl3_33 | ~spl3_44 | ~spl3_46)),
% 1.43/0.57    inference(forward_demodulation,[],[f702,f341])).
% 1.43/0.57  fof(f702,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X0)),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | (~spl3_44 | ~spl3_46)),
% 1.43/0.57    inference(superposition,[],[f502,f519])).
% 1.43/0.57  fof(f520,plain,(
% 1.43/0.57    spl3_46 | ~spl3_5 | ~spl3_31),
% 1.43/0.57    inference(avatar_split_clause,[],[f274,f270,f57,f518])).
% 1.43/0.57  fof(f270,plain,(
% 1.43/0.57    spl3_31 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.43/0.57  fof(f274,plain,(
% 1.43/0.57    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k3_xboole_0(X3,k5_xboole_0(X3,k3_xboole_0(X3,X4)))) ) | (~spl3_5 | ~spl3_31)),
% 1.43/0.57    inference(superposition,[],[f271,f58])).
% 1.43/0.57  fof(f271,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) ) | ~spl3_31),
% 1.43/0.57    inference(avatar_component_clause,[],[f270])).
% 1.43/0.57  fof(f503,plain,(
% 1.43/0.57    spl3_44),
% 1.43/0.57    inference(avatar_split_clause,[],[f37,f501])).
% 1.43/0.57  fof(f37,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f30,f25,f25,f25])).
% 1.43/0.57  fof(f25,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f2])).
% 1.43/0.57  fof(f2,axiom,(
% 1.43/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f10])).
% 1.43/0.57  fof(f10,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.43/0.57  fof(f342,plain,(
% 1.43/0.57    spl3_33 | ~spl3_5 | ~spl3_12 | ~spl3_31),
% 1.43/0.57    inference(avatar_split_clause,[],[f296,f270,f94,f57,f340])).
% 1.43/0.57  fof(f94,plain,(
% 1.43/0.57    spl3_12 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.43/0.57  fof(f296,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ) | (~spl3_5 | ~spl3_12 | ~spl3_31)),
% 1.43/0.57    inference(backward_demodulation,[],[f95,f274])).
% 1.43/0.57  fof(f95,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) ) | ~spl3_12),
% 1.43/0.57    inference(avatar_component_clause,[],[f94])).
% 1.43/0.57  fof(f272,plain,(
% 1.43/0.57    spl3_31),
% 1.43/0.57    inference(avatar_split_clause,[],[f36,f270])).
% 1.43/0.57  fof(f36,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f29,f25,f25])).
% 1.43/0.57  fof(f29,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f9])).
% 1.43/0.57  fof(f9,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.43/0.57  fof(f193,plain,(
% 1.43/0.57    ~spl3_23),
% 1.43/0.57    inference(avatar_split_clause,[],[f32,f190])).
% 1.43/0.57  fof(f32,plain,(
% 1.43/0.57    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) != k2_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))))),
% 1.43/0.57    inference(definition_unfolding,[],[f20,f25,f25,f25])).
% 1.43/0.57  fof(f20,plain,(
% 1.43/0.57    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.43/0.57    inference(cnf_transformation,[],[f18])).
% 1.43/0.57  fof(f18,plain,(
% 1.43/0.57    k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1)),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 1.43/0.57  fof(f17,plain,(
% 1.43/0.57    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1)) => (k4_xboole_0(sK0,sK2) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) & r1_tarski(sK2,sK1))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f14,plain,(
% 1.43/0.57    ? [X0,X1,X2] : (k4_xboole_0(X0,X2) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) & r1_tarski(X2,X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f12])).
% 1.43/0.57  fof(f12,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 1.43/0.57    inference(negated_conjecture,[],[f11])).
% 1.43/0.57  fof(f11,conjecture,(
% 1.43/0.57    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k4_xboole_0(X0,X2) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_xboole_1)).
% 1.43/0.57  fof(f176,plain,(
% 1.43/0.57    spl3_21 | ~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_16 | ~spl3_18),
% 1.43/0.57    inference(avatar_split_clause,[],[f156,f150,f126,f105,f94,f88,f78,f57,f173])).
% 1.43/0.57  fof(f78,plain,(
% 1.43/0.57    spl3_9 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.43/0.57  fof(f88,plain,(
% 1.43/0.57    spl3_11 <=> sK1 = k2_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.43/0.57  fof(f126,plain,(
% 1.43/0.57    spl3_16 <=> ! [X1,X0] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.43/0.57  fof(f150,plain,(
% 1.43/0.57    spl3_18 <=> k5_xboole_0(sK2,sK2) = k3_xboole_0(sK1,k1_xboole_0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.43/0.57  fof(f156,plain,(
% 1.43/0.57    k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK1,k1_xboole_0),sK2) | (~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_16 | ~spl3_18)),
% 1.43/0.57    inference(backward_demodulation,[],[f141,f154])).
% 1.43/0.57  fof(f154,plain,(
% 1.43/0.57    k3_xboole_0(sK1,k1_xboole_0) = k3_xboole_0(sK2,k1_xboole_0) | (~spl3_13 | ~spl3_18)),
% 1.43/0.57    inference(superposition,[],[f152,f106])).
% 1.43/0.57  fof(f152,plain,(
% 1.43/0.57    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK1,k1_xboole_0) | ~spl3_18),
% 1.43/0.57    inference(avatar_component_clause,[],[f150])).
% 1.43/0.57  fof(f141,plain,(
% 1.43/0.57    k3_xboole_0(sK1,sK2) = k2_xboole_0(k3_xboole_0(sK2,k1_xboole_0),sK2) | (~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_12 | ~spl3_13 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f140,f95])).
% 1.43/0.57  fof(f140,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k3_xboole_0(sK2,k1_xboole_0),sK2) | (~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_13 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f139,f106])).
% 1.43/0.57  fof(f139,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK2,sK2),sK2) | (~spl3_5 | ~spl3_9 | ~spl3_11 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f138,f80])).
% 1.43/0.57  fof(f80,plain,(
% 1.43/0.57    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_9),
% 1.43/0.57    inference(avatar_component_clause,[],[f78])).
% 1.43/0.57  fof(f138,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),sK2) | (~spl3_5 | ~spl3_11 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f137,f58])).
% 1.43/0.57  fof(f137,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k2_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)),k3_xboole_0(sK2,sK2)) | (~spl3_11 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f130,f37])).
% 1.43/0.57  fof(f130,plain,(
% 1.43/0.57    k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) = k5_xboole_0(sK2,k3_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)))) | (~spl3_11 | ~spl3_16)),
% 1.43/0.57    inference(superposition,[],[f127,f90])).
% 1.43/0.57  fof(f90,plain,(
% 1.43/0.57    sK1 = k2_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | ~spl3_11),
% 1.43/0.57    inference(avatar_component_clause,[],[f88])).
% 1.43/0.57  fof(f127,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1))) ) | ~spl3_16),
% 1.43/0.57    inference(avatar_component_clause,[],[f126])).
% 1.43/0.57  fof(f161,plain,(
% 1.43/0.57    spl3_19 | ~spl3_13 | ~spl3_18),
% 1.43/0.57    inference(avatar_split_clause,[],[f154,f150,f105,f158])).
% 1.43/0.57  fof(f153,plain,(
% 1.43/0.57    spl3_18 | ~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_16),
% 1.43/0.57    inference(avatar_split_clause,[],[f136,f126,f105,f78,f72,f57,f150])).
% 1.43/0.57  fof(f72,plain,(
% 1.43/0.57    spl3_8 <=> sK1 = k2_xboole_0(sK2,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.43/0.57  fof(f136,plain,(
% 1.43/0.57    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK1,k1_xboole_0) | (~spl3_5 | ~spl3_8 | ~spl3_9 | ~spl3_13 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f135,f80])).
% 1.43/0.57  fof(f135,plain,(
% 1.43/0.57    k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k3_xboole_0(sK1,k1_xboole_0) | (~spl3_5 | ~spl3_8 | ~spl3_13 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f134,f106])).
% 1.43/0.57  fof(f134,plain,(
% 1.43/0.57    k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,sK1) | (~spl3_5 | ~spl3_8 | ~spl3_16)),
% 1.43/0.57    inference(forward_demodulation,[],[f129,f58])).
% 1.43/0.57  fof(f129,plain,(
% 1.43/0.57    k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) | (~spl3_8 | ~spl3_16)),
% 1.43/0.57    inference(superposition,[],[f127,f74])).
% 1.43/0.57  fof(f74,plain,(
% 1.43/0.57    sK1 = k2_xboole_0(sK2,sK1) | ~spl3_8),
% 1.43/0.57    inference(avatar_component_clause,[],[f72])).
% 1.43/0.57  fof(f128,plain,(
% 1.43/0.57    spl3_16),
% 1.43/0.57    inference(avatar_split_clause,[],[f34,f126])).
% 1.43/0.57  fof(f34,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X1))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f26,f25,f25])).
% 1.43/0.57  fof(f26,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f6])).
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.43/0.57  fof(f107,plain,(
% 1.43/0.57    spl3_13 | ~spl3_4 | ~spl3_5 | ~spl3_12),
% 1.43/0.57    inference(avatar_split_clause,[],[f102,f94,f57,f52,f105])).
% 1.43/0.57  fof(f52,plain,(
% 1.43/0.57    spl3_4 <=> ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.43/0.57  fof(f102,plain,(
% 1.43/0.57    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,X0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 1.43/0.57    inference(forward_demodulation,[],[f100,f58])).
% 1.43/0.57  fof(f100,plain,(
% 1.43/0.57    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) ) | (~spl3_4 | ~spl3_12)),
% 1.43/0.57    inference(superposition,[],[f95,f53])).
% 1.43/0.57  fof(f53,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) ) | ~spl3_4),
% 1.43/0.57    inference(avatar_component_clause,[],[f52])).
% 1.43/0.57  fof(f96,plain,(
% 1.43/0.57    spl3_12),
% 1.43/0.57    inference(avatar_split_clause,[],[f31,f94])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f24,f25,f25])).
% 1.43/0.57  fof(f24,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f8])).
% 1.43/0.57  fof(f8,axiom,(
% 1.43/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.43/0.57  fof(f91,plain,(
% 1.43/0.57    spl3_11 | ~spl3_1 | ~spl3_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f86,f83,f39,f88])).
% 1.43/0.57  fof(f39,plain,(
% 1.43/0.57    spl3_1 <=> r1_tarski(sK2,sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.43/0.57  fof(f83,plain,(
% 1.43/0.57    spl3_10 <=> ! [X1,X0] : (k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.43/0.57  fof(f86,plain,(
% 1.43/0.57    sK1 = k2_xboole_0(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_10)),
% 1.43/0.57    inference(resolution,[],[f84,f41])).
% 1.43/0.57  fof(f41,plain,(
% 1.43/0.57    r1_tarski(sK2,sK1) | ~spl3_1),
% 1.43/0.57    inference(avatar_component_clause,[],[f39])).
% 1.43/0.57  fof(f84,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) ) | ~spl3_10),
% 1.43/0.57    inference(avatar_component_clause,[],[f83])).
% 1.43/0.57  fof(f85,plain,(
% 1.43/0.57    spl3_10),
% 1.43/0.57    inference(avatar_split_clause,[],[f35,f83])).
% 1.43/0.57  fof(f35,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f28,f25])).
% 1.43/0.57  fof(f28,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f16])).
% 1.43/0.57  fof(f16,plain,(
% 1.43/0.57    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f7])).
% 1.43/0.57  fof(f7,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.43/0.57  fof(f81,plain,(
% 1.43/0.57    spl3_9 | ~spl3_3 | ~spl3_8),
% 1.43/0.57    inference(avatar_split_clause,[],[f76,f72,f48,f78])).
% 1.43/0.57  fof(f48,plain,(
% 1.43/0.57    spl3_3 <=> ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.43/0.57  fof(f76,plain,(
% 1.43/0.57    sK2 = k3_xboole_0(sK2,sK1) | (~spl3_3 | ~spl3_8)),
% 1.43/0.57    inference(superposition,[],[f49,f74])).
% 1.43/0.57  fof(f49,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) ) | ~spl3_3),
% 1.43/0.57    inference(avatar_component_clause,[],[f48])).
% 1.43/0.57  fof(f75,plain,(
% 1.43/0.57    spl3_8 | ~spl3_1 | ~spl3_7),
% 1.43/0.57    inference(avatar_split_clause,[],[f70,f67,f39,f72])).
% 1.43/0.57  fof(f67,plain,(
% 1.43/0.57    spl3_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.43/0.57  fof(f70,plain,(
% 1.43/0.57    sK1 = k2_xboole_0(sK2,sK1) | (~spl3_1 | ~spl3_7)),
% 1.43/0.57    inference(resolution,[],[f68,f41])).
% 1.43/0.57  fof(f68,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_7),
% 1.43/0.57    inference(avatar_component_clause,[],[f67])).
% 1.43/0.57  fof(f69,plain,(
% 1.43/0.57    spl3_7),
% 1.43/0.57    inference(avatar_split_clause,[],[f27,f67])).
% 1.43/0.57  fof(f27,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f15,plain,(
% 1.43/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f3])).
% 1.43/0.57  fof(f3,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.43/0.57  fof(f59,plain,(
% 1.43/0.57    spl3_5 | ~spl3_2 | ~spl3_3),
% 1.43/0.57    inference(avatar_split_clause,[],[f55,f48,f44,f57])).
% 1.43/0.57  fof(f44,plain,(
% 1.43/0.57    spl3_2 <=> ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.43/0.57  fof(f55,plain,(
% 1.43/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | (~spl3_2 | ~spl3_3)),
% 1.43/0.57    inference(superposition,[],[f49,f45])).
% 1.43/0.57  fof(f45,plain,(
% 1.43/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) ) | ~spl3_2),
% 1.43/0.57    inference(avatar_component_clause,[],[f44])).
% 1.43/0.57  fof(f54,plain,(
% 1.43/0.57    spl3_4),
% 1.43/0.57    inference(avatar_split_clause,[],[f33,f52])).
% 1.43/0.57  fof(f33,plain,(
% 1.43/0.57    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.43/0.57    inference(definition_unfolding,[],[f21,f25])).
% 1.43/0.57  fof(f21,plain,(
% 1.43/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.43/0.57    inference(cnf_transformation,[],[f5])).
% 1.43/0.57  fof(f5,axiom,(
% 1.43/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.43/0.57  fof(f50,plain,(
% 1.43/0.57    spl3_3),
% 1.43/0.57    inference(avatar_split_clause,[],[f23,f48])).
% 1.43/0.57  fof(f23,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 1.43/0.57    inference(cnf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 1.43/0.57  fof(f46,plain,(
% 1.43/0.57    spl3_2),
% 1.43/0.57    inference(avatar_split_clause,[],[f22,f44])).
% 1.43/0.57  fof(f22,plain,(
% 1.43/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.43/0.57    inference(cnf_transformation,[],[f13])).
% 1.43/0.57  fof(f13,plain,(
% 1.43/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.43/0.57    inference(rectify,[],[f1])).
% 1.43/0.57  fof(f1,axiom,(
% 1.43/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.43/0.57  fof(f42,plain,(
% 1.43/0.57    spl3_1),
% 1.43/0.57    inference(avatar_split_clause,[],[f19,f39])).
% 1.43/0.57  fof(f19,plain,(
% 1.43/0.57    r1_tarski(sK2,sK1)),
% 1.43/0.57    inference(cnf_transformation,[],[f18])).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (16768)------------------------------
% 1.43/0.57  % (16768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (16768)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (16768)Memory used [KB]: 7419
% 1.43/0.57  % (16768)Time elapsed: 0.154 s
% 1.43/0.57  % (16768)------------------------------
% 1.43/0.57  % (16768)------------------------------
% 1.43/0.57  % (16760)Success in time 0.211 s
%------------------------------------------------------------------------------
