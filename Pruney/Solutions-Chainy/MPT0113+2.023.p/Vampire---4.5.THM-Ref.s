%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 163 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  284 ( 414 expanded)
%              Number of equality atoms :   65 (  99 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f60,f64,f68,f72,f80,f92,f100,f104,f108,f112,f122,f126,f195,f229,f247,f272,f316,f549,f563,f582])).

fof(f582,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22
    | spl3_23
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_47
    | ~ spl3_49 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22
    | spl3_23
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_47
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f555,f580])).

fof(f580,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),X0))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22
    | ~ spl3_25
    | ~ spl3_30
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f569,f278])).

fof(f278,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f274,f241])).

fof(f241,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f233,f175])).

fof(f175,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f171,f67])).

fof(f67,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f171,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_17 ),
    inference(superposition,[],[f121,f63])).

fof(f63,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl3_4
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f121,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_17
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f233,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_22 ),
    inference(superposition,[],[f228,f63])).

fof(f228,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f274,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)
    | ~ spl3_22
    | ~ spl3_25 ),
    inference(superposition,[],[f228,f271])).

fof(f271,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_25
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f569,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X0))
    | ~ spl3_30
    | ~ spl3_49 ),
    inference(unit_resulting_resolution,[],[f315,f562])).

fof(f562,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != X0
        | r1_xboole_0(X0,k2_xboole_0(X0,X1)) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl3_49
  <=> ! [X1,X0] :
        ( k1_xboole_0 != X0
        | r1_xboole_0(X0,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f315,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl3_30
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f555,plain,
    ( ! [X0] : ~ r1_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),X0))
    | spl3_23
    | ~ spl3_47 ),
    inference(unit_resulting_resolution,[],[f246,f548])).

fof(f548,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,k2_xboole_0(X0,X1))
        | k1_xboole_0 = X0 )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl3_47
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X0,k2_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f246,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_23
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f563,plain,
    ( spl3_49
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f155,f102,f78,f561])).

fof(f78,plain,
    ( spl3_8
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f102,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != X0
        | r1_xboole_0(X0,k2_xboole_0(X0,X1)) )
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(superposition,[],[f103,f79])).

fof(f79,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f102])).

fof(f549,plain,
    ( spl3_47
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f148,f98,f78,f547])).

fof(f98,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f148,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | ~ r1_xboole_0(X0,k2_xboole_0(X0,X1)) )
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(superposition,[],[f99,f79])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f316,plain,
    ( spl3_30
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f162,f110,f48,f313])).

fof(f48,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f162,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f50,f111])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f110])).

fof(f50,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f272,plain,
    ( spl3_25
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f198,f90,f57,f269])).

fof(f57,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f90,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f198,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f58,f91])).

fof(f91,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f58,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f247,plain,
    ( ~ spl3_23
    | spl3_2
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f157,f106,f53,f244])).

fof(f53,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f157,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_2
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f55,f107])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f106])).

fof(f55,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f229,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f45,f227])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f195,plain,
    ( spl3_3
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f179,f124,f70,f48,f57])).

fof(f70,plain,
    ( spl3_6
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f124,plain,
    ( spl3_18
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f179,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f71,f50,f125])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f71,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f126,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f46,f124])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f122,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f35,f120])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f112,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f43,f110])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f108,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f104,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f41,f102])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f100,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f40,f98])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f92,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f38,f90])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f80,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f33,f78])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f70])).

fof(f31,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f68,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f30,f66])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f62])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f60,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f28,f57,f53])).

fof(f28,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f51,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f27,f48])).

fof(f27,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (4354)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.45  % (4343)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (4353)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (4344)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (4349)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (4346)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (4342)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (4352)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (4356)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (4347)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (4345)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (4348)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (4359)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (4351)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (4358)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (4355)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (4347)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f589,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f51,f60,f64,f68,f72,f80,f92,f100,f104,f108,f112,f122,f126,f195,f229,f247,f272,f316,f549,f563,f582])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    ~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_22 | spl3_23 | ~spl3_25 | ~spl3_30 | ~spl3_47 | ~spl3_49),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f581])).
% 0.21/0.50  fof(f581,plain,(
% 0.21/0.50    $false | (~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_22 | spl3_23 | ~spl3_25 | ~spl3_30 | ~spl3_47 | ~spl3_49)),
% 0.21/0.50    inference(subsumption_resolution,[],[f555,f580])).
% 0.21/0.50  fof(f580,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),X0))) ) | (~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_22 | ~spl3_25 | ~spl3_30 | ~spl3_49)),
% 0.21/0.50    inference(forward_demodulation,[],[f569,f278])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,sK2))) ) | (~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_22 | ~spl3_25)),
% 0.21/0.50    inference(forward_demodulation,[],[f274,f241])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_17 | ~spl3_22)),
% 0.21/0.50    inference(forward_demodulation,[],[f233,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl3_4 | ~spl3_5 | ~spl3_17)),
% 0.21/0.50    inference(forward_demodulation,[],[f171,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) ) | (~spl3_4 | ~spl3_17)),
% 0.21/0.50    inference(superposition,[],[f121,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_4 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_17),
% 0.21/0.50    inference(avatar_component_clause,[],[f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    spl3_17 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_4 | ~spl3_22)),
% 0.21/0.50    inference(superposition,[],[f228,f63])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) ) | ~spl3_22),
% 0.21/0.50    inference(avatar_component_clause,[],[f227])).
% 0.21/0.50  fof(f227,plain,(
% 0.21/0.50    spl3_22 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(X0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X0),k1_xboole_0)) ) | (~spl3_22 | ~spl3_25)),
% 0.21/0.50    inference(superposition,[],[f228,f271])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl3_25),
% 0.21/0.50    inference(avatar_component_clause,[],[f269])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    spl3_25 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.50  fof(f569,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),X0))) ) | (~spl3_30 | ~spl3_49)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f315,f562])).
% 0.21/0.50  fof(f562,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl3_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f561])).
% 0.21/0.50  fof(f561,plain,(
% 0.21/0.50    spl3_49 <=> ! [X1,X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,k2_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f313])).
% 0.21/0.50  fof(f313,plain,(
% 0.21/0.50    spl3_30 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.50  fof(f555,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),X0))) ) | (spl3_23 | ~spl3_47)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f246,f548])).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X0,X1)) | k1_xboole_0 = X0) ) | ~spl3_47),
% 0.21/0.50    inference(avatar_component_clause,[],[f547])).
% 0.21/0.50  fof(f547,plain,(
% 0.21/0.50    spl3_47 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,k2_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f244])).
% 0.21/0.50  fof(f244,plain,(
% 0.21/0.50    spl3_23 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f563,plain,(
% 0.21/0.50    spl3_49 | ~spl3_8 | ~spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f155,f102,f78,f561])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl3_8 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    spl3_14 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl3_8 | ~spl3_14)),
% 0.21/0.50    inference(superposition,[],[f103,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f102])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    spl3_47 | ~spl3_8 | ~spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f148,f98,f78,f547])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_13 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,k2_xboole_0(X0,X1))) ) | (~spl3_8 | ~spl3_13)),
% 0.21/0.50    inference(superposition,[],[f99,f79])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f316,plain,(
% 0.21/0.50    spl3_30 | ~spl3_1 | ~spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f110,f48,f313])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl3_16 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_16)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f50,f111])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) ) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f48])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    spl3_25 | ~spl3_3 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f198,f90,f57,f269])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl3_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(sK0,sK2) | (~spl3_3 | ~spl3_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f58,f91])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f57])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~spl3_23 | spl3_2 | ~spl3_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f157,f106,f53,f244])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    spl3_15 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_2 | ~spl3_15)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f55,f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) ) | ~spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f106])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f53])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl3_22),
% 0.21/0.50    inference(avatar_split_clause,[],[f45,f227])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    spl3_3 | ~spl3_1 | ~spl3_6 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f179,f124,f70,f48,f57])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl3_6 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    spl3_18 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    r1_xboole_0(sK0,sK2) | (~spl3_1 | ~spl3_6 | ~spl3_18)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f71,f50,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f124])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f46,f124])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    spl3_17),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f120])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f43,f110])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl3_15),
% 0.21/0.50    inference(avatar_split_clause,[],[f42,f106])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl3_14),
% 0.21/0.50    inference(avatar_split_clause,[],[f41,f102])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f98])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f90])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f78])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f70])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f30,f66])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f62])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f57,f53])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f16])).
% 0.21/0.50  fof(f16,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f48])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4347)------------------------------
% 0.21/0.50  % (4347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4347)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4347)Memory used [KB]: 6396
% 0.21/0.50  % (4347)Time elapsed: 0.079 s
% 0.21/0.50  % (4347)------------------------------
% 0.21/0.50  % (4347)------------------------------
% 0.21/0.50  % (4341)Success in time 0.149 s
%------------------------------------------------------------------------------
