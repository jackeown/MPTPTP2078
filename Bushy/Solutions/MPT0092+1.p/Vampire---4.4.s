%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t85_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:34 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 120 expanded)
%              Number of leaves         :   22 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :  154 ( 240 expanded)
%              Number of equality atoms :   35 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f60,f67,f77,f86,f94,f131,f138,f152,f181,f188,f196])).

fof(f196,plain,
    ( ~ spl3_6
    | ~ spl3_12
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f194,f76])).

fof(f76,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f194,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f190,f151])).

fof(f151,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl3_17
  <=> ~ v1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f190,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(sK0,X0),sK1) = k1_xboole_0
    | ~ spl3_12 ),
    inference(superposition,[],[f166,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',commutativity_k3_xboole_0)).

fof(f166,plain,
    ( ! [X4] : k4_xboole_0(k3_xboole_0(X4,sK0),sK1) = k1_xboole_0
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f155,f37])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',t2_boole)).

fof(f155,plain,
    ( ! [X4] : k4_xboole_0(k3_xboole_0(X4,sK0),sK1) = k3_xboole_0(X4,k1_xboole_0)
    | ~ spl3_12 ),
    inference(superposition,[],[f46,f130])).

fof(f130,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl3_12
  <=> k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',t49_xboole_1)).

fof(f188,plain,
    ( ~ spl3_21
    | spl3_15 ),
    inference(avatar_split_clause,[],[f164,f136,f186])).

fof(f186,plain,
    ( spl3_21
  <=> k4_xboole_0(k3_xboole_0(sK0,sK2),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f136,plain,
    ( spl3_15
  <=> k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f164,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK2),sK1) != k1_xboole_0
    | ~ spl3_15 ),
    inference(superposition,[],[f137,f46])).

fof(f137,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != k1_xboole_0
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f181,plain,
    ( ~ spl3_19
    | spl3_11 ),
    inference(avatar_split_clause,[],[f107,f92,f179])).

fof(f179,plain,
    ( spl3_19
  <=> k3_xboole_0(k4_xboole_0(sK2,sK1),sK0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f92,plain,
    ( spl3_11
  <=> ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f107,plain,
    ( k3_xboole_0(k4_xboole_0(sK2,sK1),sK0) != k1_xboole_0
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f93,f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',d7_xboole_0)).

fof(f93,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f152,plain,
    ( ~ spl3_17
    | ~ spl3_6
    | spl3_15 ),
    inference(avatar_split_clause,[],[f143,f136,f75,f150])).

fof(f143,plain,
    ( ~ v1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK2),sK1))
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f142,f46])).

fof(f142,plain,
    ( ~ v1_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)))
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f76,f137,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',t8_boole)).

fof(f138,plain,
    ( ~ spl3_15
    | spl3_5 ),
    inference(avatar_split_clause,[],[f106,f65,f136])).

fof(f65,plain,
    ( spl3_5
  <=> ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f106,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK2,sK1)) != k1_xboole_0
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f66,f43])).

fof(f66,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f131,plain,
    ( spl3_12
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f123,f58,f129])).

fof(f58,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f123,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f59,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',l32_xboole_1)).

fof(f59,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f94,plain,
    ( ~ spl3_11
    | spl3_5 ),
    inference(avatar_split_clause,[],[f87,f65,f92])).

fof(f87,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f66,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',symmetry_r1_xboole_0)).

fof(f86,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f68,f51,f84])).

fof(f84,plain,
    ( spl3_8
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f51,plain,
    ( spl3_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f68,plain,
    ( k1_xboole_0 = o_0_0_xboole_0
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',t6_boole)).

fof(f52,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,
    ( spl3_6
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f70,f51,f75])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_0 ),
    inference(backward_demodulation,[],[f68,f52])).

fof(f67,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f33,f65])).

fof(f33,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',t85_xboole_1)).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f34,f51])).

fof(f34,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t85_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
