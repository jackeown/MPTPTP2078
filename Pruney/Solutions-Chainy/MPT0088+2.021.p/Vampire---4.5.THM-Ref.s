%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:33 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 227 expanded)
%              Number of leaves         :   37 ( 111 expanded)
%              Depth                    :    6
%              Number of atoms          :  289 ( 487 expanded)
%              Number of equality atoms :   87 ( 167 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f58,f62,f68,f83,f94,f98,f242,f246,f252,f259,f284,f288,f514,f770,f1366,f1482,f1606,f1986,f2366,f2510,f2625,f2652])).

fof(f2652,plain,
    ( ~ spl3_7
    | spl3_24
    | ~ spl3_66
    | ~ spl3_79 ),
    inference(avatar_contradiction_clause,[],[f2651])).

fof(f2651,plain,
    ( $false
    | ~ spl3_7
    | spl3_24
    | ~ spl3_66
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f2650,f67])).

fof(f67,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_7
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f2650,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | spl3_24
    | ~ spl3_66
    | ~ spl3_79 ),
    inference(backward_demodulation,[],[f251,f2627])).

fof(f2627,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ spl3_66
    | ~ spl3_79 ),
    inference(superposition,[],[f1985,f2624])).

fof(f2624,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f2622])).

fof(f2622,plain,
    ( spl3_79
  <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f1985,plain,
    ( ! [X33,X31,X32] : k4_xboole_0(X33,k4_xboole_0(X31,k2_xboole_0(X32,X33))) = X33
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f1984])).

fof(f1984,plain,
    ( spl3_66
  <=> ! [X32,X31,X33] : k4_xboole_0(X33,k4_xboole_0(X31,k2_xboole_0(X32,X33))) = X33 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f251,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl3_24
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f2625,plain,
    ( spl3_79
    | ~ spl3_63
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f2572,f2508,f1604,f2622])).

fof(f1604,plain,
    ( spl3_63
  <=> ! [X3,X2] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f2508,plain,
    ( spl3_75
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f2572,plain,
    ( k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_63
    | ~ spl3_75 ),
    inference(superposition,[],[f2509,f1605])).

fof(f1605,plain,
    ( ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f1604])).

fof(f2509,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f2508])).

fof(f2510,plain,
    ( spl3_75
    | ~ spl3_12
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f2415,f2364,f96,f2508])).

fof(f96,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f2364,plain,
    ( spl3_70
  <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f2415,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_12
    | ~ spl3_70 ),
    inference(forward_demodulation,[],[f2377,f2365])).

fof(f2365,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f2364])).

fof(f2377,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_12
    | ~ spl3_70 ),
    inference(superposition,[],[f2365,f97])).

fof(f97,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f2366,plain,
    ( spl3_70
    | ~ spl3_27
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f521,f511,f282,f2364])).

fof(f282,plain,
    ( spl3_27
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f511,plain,
    ( spl3_34
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f521,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_27
    | ~ spl3_34 ),
    inference(superposition,[],[f283,f513])).

fof(f513,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f511])).

fof(f283,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f282])).

fof(f1986,plain,
    ( spl3_66
    | ~ spl3_27
    | ~ spl3_59 ),
    inference(avatar_split_clause,[],[f1498,f1480,f282,f1984])).

fof(f1480,plain,
    ( spl3_59
  <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f1498,plain,
    ( ! [X33,X31,X32] : k4_xboole_0(X33,k4_xboole_0(X31,k2_xboole_0(X32,X33))) = X33
    | ~ spl3_27
    | ~ spl3_59 ),
    inference(superposition,[],[f1481,f283])).

fof(f1481,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f1480])).

fof(f1606,plain,
    ( spl3_63
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1448,f1364,f286,f96,f92,f47,f1604])).

fof(f47,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f92,plain,
    ( spl3_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f286,plain,
    ( spl3_28
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1364,plain,
    ( spl3_57
  <=> ! [X3,X4] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f1448,plain,
    ( ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(backward_demodulation,[],[f125,f1442])).

fof(f1442,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(forward_demodulation,[],[f1399,f48])).

fof(f48,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f1399,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4))
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(superposition,[],[f287,f1365])).

fof(f1365,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f1364])).

fof(f287,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f286])).

fof(f125,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(superposition,[],[f93,f97])).

fof(f93,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f1482,plain,
    ( spl3_59
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f1442,f1364,f286,f47,f1480])).

fof(f1366,plain,
    ( spl3_57
    | ~ spl3_10
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f1226,f768,f81,f1364])).

fof(f81,plain,
    ( spl3_10
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f768,plain,
    ( spl3_46
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1226,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))
    | ~ spl3_10
    | ~ spl3_46 ),
    inference(superposition,[],[f769,f82])).

fof(f82,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f769,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f768])).

fof(f770,plain,(
    spl3_46 ),
    inference(avatar_split_clause,[],[f35,f768])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f30,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f514,plain,
    ( spl3_34
    | ~ spl3_3
    | ~ spl3_25
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f499,f286,f256,f47,f511])).

fof(f256,plain,
    ( spl3_25
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f499,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_25
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f475,f48])).

fof(f475,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_25
    | ~ spl3_28 ),
    inference(superposition,[],[f287,f258])).

fof(f258,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f256])).

fof(f288,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f32,f286])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f284,plain,(
    spl3_27 ),
    inference(avatar_split_clause,[],[f31,f282])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f259,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f253,f244,f37,f256])).

fof(f37,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f244,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f253,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_1
    | ~ spl3_23 ),
    inference(resolution,[],[f245,f39])).

fof(f39,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f245,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f244])).

fof(f252,plain,
    ( ~ spl3_24
    | spl3_2
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f247,f240,f42,f249])).

fof(f42,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f240,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f247,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))
    | spl3_2
    | ~ spl3_22 ),
    inference(resolution,[],[f241,f44])).

fof(f44,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f241,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f240])).

fof(f246,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f34,f244])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f242,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f33,f240])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f26,f96])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f94,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f25,f92])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f83,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f63,f60,f51,f81])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f63,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(resolution,[],[f61,f52])).

fof(f52,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f68,plain,
    ( spl3_7
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f60,f56,f66])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f64,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f61,f57])).

fof(f57,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f58,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f54,f51,f47,f56])).

fof(f54,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f52,f48])).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f45,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:12:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (29000)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (28993)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (28996)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (28988)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (29002)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (29001)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (28995)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (28989)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (28991)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (28992)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (28994)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28998)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (28990)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (29003)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (28997)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (29005)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.43/0.54  % (28999)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.43/0.55  % (29004)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.55/0.59  % (28995)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f2657,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f58,f62,f68,f83,f94,f98,f242,f246,f252,f259,f284,f288,f514,f770,f1366,f1482,f1606,f1986,f2366,f2510,f2625,f2652])).
% 1.55/0.59  fof(f2652,plain,(
% 1.55/0.59    ~spl3_7 | spl3_24 | ~spl3_66 | ~spl3_79),
% 1.55/0.59    inference(avatar_contradiction_clause,[],[f2651])).
% 1.55/0.59  fof(f2651,plain,(
% 1.55/0.59    $false | (~spl3_7 | spl3_24 | ~spl3_66 | ~spl3_79)),
% 1.55/0.59    inference(subsumption_resolution,[],[f2650,f67])).
% 1.55/0.59  fof(f67,plain,(
% 1.55/0.59    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl3_7),
% 1.55/0.59    inference(avatar_component_clause,[],[f66])).
% 1.55/0.59  fof(f66,plain,(
% 1.55/0.59    spl3_7 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.55/0.59  fof(f2650,plain,(
% 1.55/0.59    k1_xboole_0 != k4_xboole_0(sK1,sK1) | (spl3_24 | ~spl3_66 | ~spl3_79)),
% 1.55/0.59    inference(backward_demodulation,[],[f251,f2627])).
% 1.55/0.59  fof(f2627,plain,(
% 1.55/0.59    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | (~spl3_66 | ~spl3_79)),
% 1.55/0.59    inference(superposition,[],[f1985,f2624])).
% 1.55/0.59  fof(f2624,plain,(
% 1.55/0.59    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~spl3_79),
% 1.55/0.59    inference(avatar_component_clause,[],[f2622])).
% 1.55/0.59  fof(f2622,plain,(
% 1.55/0.59    spl3_79 <=> k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 1.55/0.59  fof(f1985,plain,(
% 1.55/0.59    ( ! [X33,X31,X32] : (k4_xboole_0(X33,k4_xboole_0(X31,k2_xboole_0(X32,X33))) = X33) ) | ~spl3_66),
% 1.55/0.59    inference(avatar_component_clause,[],[f1984])).
% 1.55/0.59  fof(f1984,plain,(
% 1.55/0.59    spl3_66 <=> ! [X32,X31,X33] : k4_xboole_0(X33,k4_xboole_0(X31,k2_xboole_0(X32,X33))) = X33),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 1.55/0.59  fof(f251,plain,(
% 1.55/0.59    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | spl3_24),
% 1.55/0.59    inference(avatar_component_clause,[],[f249])).
% 1.55/0.59  fof(f249,plain,(
% 1.55/0.59    spl3_24 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.55/0.59  fof(f2625,plain,(
% 1.55/0.59    spl3_79 | ~spl3_63 | ~spl3_75),
% 1.55/0.59    inference(avatar_split_clause,[],[f2572,f2508,f1604,f2622])).
% 1.55/0.59  fof(f1604,plain,(
% 1.55/0.59    spl3_63 <=> ! [X3,X2] : k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 1.55/0.59  fof(f2508,plain,(
% 1.55/0.59    spl3_75 <=> ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 1.55/0.59  fof(f2572,plain,(
% 1.55/0.59    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | (~spl3_63 | ~spl3_75)),
% 1.55/0.59    inference(superposition,[],[f2509,f1605])).
% 1.55/0.59  fof(f1605,plain,(
% 1.55/0.59    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) ) | ~spl3_63),
% 1.55/0.59    inference(avatar_component_clause,[],[f1604])).
% 1.55/0.59  fof(f2509,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | ~spl3_75),
% 1.55/0.59    inference(avatar_component_clause,[],[f2508])).
% 1.55/0.59  fof(f2510,plain,(
% 1.55/0.59    spl3_75 | ~spl3_12 | ~spl3_70),
% 1.55/0.59    inference(avatar_split_clause,[],[f2415,f2364,f96,f2508])).
% 1.55/0.59  fof(f96,plain,(
% 1.55/0.59    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.55/0.59  fof(f2364,plain,(
% 1.55/0.59    spl3_70 <=> ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.55/0.59  fof(f2415,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | (~spl3_12 | ~spl3_70)),
% 1.55/0.59    inference(forward_demodulation,[],[f2377,f2365])).
% 1.55/0.59  fof(f2365,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) ) | ~spl3_70),
% 1.55/0.59    inference(avatar_component_clause,[],[f2364])).
% 1.55/0.59  fof(f2377,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,sK2)))) ) | (~spl3_12 | ~spl3_70)),
% 1.55/0.59    inference(superposition,[],[f2365,f97])).
% 1.55/0.59  fof(f97,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) ) | ~spl3_12),
% 1.55/0.59    inference(avatar_component_clause,[],[f96])).
% 1.55/0.59  fof(f2366,plain,(
% 1.55/0.59    spl3_70 | ~spl3_27 | ~spl3_34),
% 1.55/0.59    inference(avatar_split_clause,[],[f521,f511,f282,f2364])).
% 1.55/0.59  fof(f282,plain,(
% 1.55/0.59    spl3_27 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.55/0.59  fof(f511,plain,(
% 1.55/0.59    spl3_34 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.55/0.59  fof(f521,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) ) | (~spl3_27 | ~spl3_34)),
% 1.55/0.59    inference(superposition,[],[f283,f513])).
% 1.55/0.59  fof(f513,plain,(
% 1.55/0.59    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_34),
% 1.55/0.59    inference(avatar_component_clause,[],[f511])).
% 1.55/0.59  fof(f283,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_27),
% 1.55/0.59    inference(avatar_component_clause,[],[f282])).
% 1.55/0.59  fof(f1986,plain,(
% 1.55/0.59    spl3_66 | ~spl3_27 | ~spl3_59),
% 1.55/0.59    inference(avatar_split_clause,[],[f1498,f1480,f282,f1984])).
% 1.55/0.59  fof(f1480,plain,(
% 1.55/0.59    spl3_59 <=> ! [X5,X4] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.55/0.59  fof(f1498,plain,(
% 1.55/0.59    ( ! [X33,X31,X32] : (k4_xboole_0(X33,k4_xboole_0(X31,k2_xboole_0(X32,X33))) = X33) ) | (~spl3_27 | ~spl3_59)),
% 1.55/0.59    inference(superposition,[],[f1481,f283])).
% 1.55/0.59  fof(f1481,plain,(
% 1.55/0.59    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | ~spl3_59),
% 1.55/0.59    inference(avatar_component_clause,[],[f1480])).
% 1.55/0.59  fof(f1606,plain,(
% 1.55/0.59    spl3_63 | ~spl3_3 | ~spl3_11 | ~spl3_12 | ~spl3_28 | ~spl3_57),
% 1.55/0.59    inference(avatar_split_clause,[],[f1448,f1364,f286,f96,f92,f47,f1604])).
% 1.55/0.59  fof(f47,plain,(
% 1.55/0.59    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.55/0.59  fof(f92,plain,(
% 1.55/0.59    spl3_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.55/0.59  fof(f286,plain,(
% 1.55/0.59    spl3_28 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.55/0.59  fof(f1364,plain,(
% 1.55/0.59    spl3_57 <=> ! [X3,X4] : k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.55/0.59  fof(f1448,plain,(
% 1.55/0.59    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = X2) ) | (~spl3_3 | ~spl3_11 | ~spl3_12 | ~spl3_28 | ~spl3_57)),
% 1.55/0.59    inference(backward_demodulation,[],[f125,f1442])).
% 1.55/0.59  fof(f1442,plain,(
% 1.55/0.59    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = X4) ) | (~spl3_3 | ~spl3_28 | ~spl3_57)),
% 1.55/0.59    inference(forward_demodulation,[],[f1399,f48])).
% 1.55/0.59  fof(f48,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 1.55/0.59    inference(avatar_component_clause,[],[f47])).
% 1.55/0.59  fof(f1399,plain,(
% 1.55/0.59    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = k4_xboole_0(X4,k4_xboole_0(X5,X4))) ) | (~spl3_28 | ~spl3_57)),
% 1.55/0.59    inference(superposition,[],[f287,f1365])).
% 1.55/0.59  fof(f1365,plain,(
% 1.55/0.59    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))) ) | ~spl3_57),
% 1.55/0.59    inference(avatar_component_clause,[],[f1364])).
% 1.55/0.59  fof(f287,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_28),
% 1.55/0.59    inference(avatar_component_clause,[],[f286])).
% 1.55/0.59  fof(f125,plain,(
% 1.55/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ) | (~spl3_11 | ~spl3_12)),
% 1.55/0.59    inference(superposition,[],[f93,f97])).
% 1.55/0.59  fof(f93,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl3_11),
% 1.55/0.59    inference(avatar_component_clause,[],[f92])).
% 1.55/0.59  fof(f1482,plain,(
% 1.55/0.59    spl3_59 | ~spl3_3 | ~spl3_28 | ~spl3_57),
% 1.55/0.59    inference(avatar_split_clause,[],[f1442,f1364,f286,f47,f1480])).
% 1.55/0.59  fof(f1366,plain,(
% 1.55/0.59    spl3_57 | ~spl3_10 | ~spl3_46),
% 1.55/0.59    inference(avatar_split_clause,[],[f1226,f768,f81,f1364])).
% 1.55/0.59  fof(f81,plain,(
% 1.55/0.59    spl3_10 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.55/0.59  fof(f768,plain,(
% 1.55/0.59    spl3_46 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.55/0.59  fof(f1226,plain,(
% 1.55/0.59    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(X3,k4_xboole_0(X3,k4_xboole_0(X4,X3)))) ) | (~spl3_10 | ~spl3_46)),
% 1.55/0.59    inference(superposition,[],[f769,f82])).
% 1.55/0.59  fof(f82,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_10),
% 1.55/0.59    inference(avatar_component_clause,[],[f81])).
% 1.55/0.59  fof(f769,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) ) | ~spl3_46),
% 1.55/0.59    inference(avatar_component_clause,[],[f768])).
% 1.55/0.59  fof(f770,plain,(
% 1.55/0.59    spl3_46),
% 1.55/0.59    inference(avatar_split_clause,[],[f35,f768])).
% 1.55/0.59  fof(f35,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f30,f23,f23])).
% 1.55/0.59  fof(f23,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f9])).
% 1.55/0.59  fof(f9,axiom,(
% 1.55/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.55/0.59  fof(f30,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f10])).
% 1.55/0.59  fof(f10,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.55/0.59  fof(f514,plain,(
% 1.55/0.59    spl3_34 | ~spl3_3 | ~spl3_25 | ~spl3_28),
% 1.55/0.59    inference(avatar_split_clause,[],[f499,f286,f256,f47,f511])).
% 1.55/0.59  fof(f256,plain,(
% 1.55/0.59    spl3_25 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.55/0.59  fof(f499,plain,(
% 1.55/0.59    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_25 | ~spl3_28)),
% 1.55/0.59    inference(forward_demodulation,[],[f475,f48])).
% 1.55/0.59  fof(f475,plain,(
% 1.55/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_25 | ~spl3_28)),
% 1.55/0.59    inference(superposition,[],[f287,f258])).
% 1.55/0.59  fof(f258,plain,(
% 1.55/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_25),
% 1.55/0.59    inference(avatar_component_clause,[],[f256])).
% 1.55/0.59  fof(f288,plain,(
% 1.55/0.59    spl3_28),
% 1.55/0.59    inference(avatar_split_clause,[],[f32,f286])).
% 1.55/0.59  fof(f32,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.55/0.59    inference(definition_unfolding,[],[f24,f23])).
% 1.55/0.59  fof(f24,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.55/0.59  fof(f284,plain,(
% 1.55/0.59    spl3_27),
% 1.55/0.59    inference(avatar_split_clause,[],[f31,f282])).
% 1.55/0.59  fof(f31,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.55/0.59    inference(cnf_transformation,[],[f7])).
% 1.55/0.59  fof(f7,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.55/0.59  fof(f259,plain,(
% 1.55/0.59    spl3_25 | ~spl3_1 | ~spl3_23),
% 1.55/0.59    inference(avatar_split_clause,[],[f253,f244,f37,f256])).
% 1.55/0.59  fof(f37,plain,(
% 1.55/0.59    spl3_1 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.55/0.59  fof(f244,plain,(
% 1.55/0.59    spl3_23 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.55/0.59  fof(f253,plain,(
% 1.55/0.59    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | (~spl3_1 | ~spl3_23)),
% 1.55/0.59    inference(resolution,[],[f245,f39])).
% 1.55/0.59  fof(f39,plain,(
% 1.55/0.59    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.55/0.59    inference(avatar_component_clause,[],[f37])).
% 1.55/0.59  fof(f245,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_23),
% 1.55/0.59    inference(avatar_component_clause,[],[f244])).
% 1.55/0.59  fof(f252,plain,(
% 1.55/0.59    ~spl3_24 | spl3_2 | ~spl3_22),
% 1.55/0.59    inference(avatar_split_clause,[],[f247,f240,f42,f249])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    spl3_2 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.55/0.59  fof(f240,plain,(
% 1.55/0.59    spl3_22 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.55/0.59  fof(f247,plain,(
% 1.55/0.59    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) | (spl3_2 | ~spl3_22)),
% 1.55/0.59    inference(resolution,[],[f241,f44])).
% 1.55/0.59  fof(f44,plain,(
% 1.55/0.59    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | spl3_2),
% 1.55/0.59    inference(avatar_component_clause,[],[f42])).
% 1.55/0.59  fof(f241,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_22),
% 1.55/0.59    inference(avatar_component_clause,[],[f240])).
% 1.55/0.59  fof(f246,plain,(
% 1.55/0.59    spl3_23),
% 1.55/0.59    inference(avatar_split_clause,[],[f34,f244])).
% 1.55/0.59  fof(f34,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.59    inference(definition_unfolding,[],[f27,f23])).
% 1.55/0.59  fof(f27,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f18])).
% 1.55/0.59  fof(f18,plain,(
% 1.55/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.55/0.59    inference(nnf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.55/0.59  fof(f242,plain,(
% 1.55/0.59    spl3_22),
% 1.55/0.59    inference(avatar_split_clause,[],[f33,f240])).
% 1.55/0.59  fof(f33,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.55/0.59    inference(definition_unfolding,[],[f28,f23])).
% 1.55/0.59  fof(f28,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f18])).
% 1.55/0.59  fof(f98,plain,(
% 1.55/0.59    spl3_12),
% 1.55/0.59    inference(avatar_split_clause,[],[f26,f96])).
% 1.55/0.59  fof(f26,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f4])).
% 1.55/0.59  fof(f4,axiom,(
% 1.55/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.55/0.59  fof(f94,plain,(
% 1.55/0.59    spl3_11),
% 1.55/0.59    inference(avatar_split_clause,[],[f25,f92])).
% 1.55/0.59  fof(f25,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f6])).
% 1.55/0.59  fof(f6,axiom,(
% 1.55/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.55/0.59  fof(f83,plain,(
% 1.55/0.59    spl3_10 | ~spl3_4 | ~spl3_6),
% 1.55/0.59    inference(avatar_split_clause,[],[f63,f60,f51,f81])).
% 1.55/0.59  fof(f51,plain,(
% 1.55/0.59    spl3_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.55/0.59  fof(f60,plain,(
% 1.55/0.59    spl3_6 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.55/0.59  fof(f63,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_4 | ~spl3_6)),
% 1.55/0.59    inference(resolution,[],[f61,f52])).
% 1.55/0.59  fof(f52,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 1.55/0.59    inference(avatar_component_clause,[],[f51])).
% 1.55/0.59  fof(f61,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_6),
% 1.55/0.59    inference(avatar_component_clause,[],[f60])).
% 1.55/0.59  fof(f68,plain,(
% 1.55/0.59    spl3_7 | ~spl3_5 | ~spl3_6),
% 1.55/0.59    inference(avatar_split_clause,[],[f64,f60,f56,f66])).
% 1.55/0.59  fof(f56,plain,(
% 1.55/0.59    spl3_5 <=> ! [X0] : r1_tarski(X0,X0)),
% 1.55/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.55/0.59  fof(f64,plain,(
% 1.55/0.59    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl3_5 | ~spl3_6)),
% 1.55/0.59    inference(resolution,[],[f61,f57])).
% 1.55/0.59  fof(f57,plain,(
% 1.55/0.59    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_5),
% 1.55/0.59    inference(avatar_component_clause,[],[f56])).
% 1.55/0.59  fof(f62,plain,(
% 1.55/0.59    spl3_6),
% 1.55/0.59    inference(avatar_split_clause,[],[f29,f60])).
% 1.55/0.59  fof(f29,plain,(
% 1.55/0.59    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f15])).
% 1.55/0.59  fof(f15,plain,(
% 1.55/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 1.55/0.59    inference(ennf_transformation,[],[f13])).
% 1.55/0.59  fof(f13,plain,(
% 1.55/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 1.55/0.59    inference(unused_predicate_definition_removal,[],[f2])).
% 1.55/0.59  fof(f2,axiom,(
% 1.55/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.55/0.59  fof(f58,plain,(
% 1.55/0.59    spl3_5 | ~spl3_3 | ~spl3_4),
% 1.55/0.59    inference(avatar_split_clause,[],[f54,f51,f47,f56])).
% 1.55/0.59  fof(f54,plain,(
% 1.55/0.59    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_3 | ~spl3_4)),
% 1.55/0.59    inference(superposition,[],[f52,f48])).
% 1.55/0.59  fof(f53,plain,(
% 1.55/0.59    spl3_4),
% 1.55/0.59    inference(avatar_split_clause,[],[f22,f51])).
% 1.55/0.59  fof(f22,plain,(
% 1.55/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f3])).
% 1.55/0.59  fof(f3,axiom,(
% 1.55/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.55/0.59  fof(f49,plain,(
% 1.55/0.59    spl3_3),
% 1.55/0.59    inference(avatar_split_clause,[],[f21,f47])).
% 1.55/0.59  fof(f21,plain,(
% 1.55/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.59    inference(cnf_transformation,[],[f5])).
% 1.55/0.59  fof(f5,axiom,(
% 1.55/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.55/0.59  fof(f45,plain,(
% 1.55/0.59    ~spl3_2),
% 1.55/0.59    inference(avatar_split_clause,[],[f20,f42])).
% 1.55/0.59  fof(f20,plain,(
% 1.55/0.59    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  fof(f17,plain,(
% 1.55/0.59    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 1.55/0.59  fof(f16,plain,(
% 1.55/0.59    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f14,plain,(
% 1.55/0.59    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.55/0.59    inference(ennf_transformation,[],[f12])).
% 1.55/0.59  fof(f12,negated_conjecture,(
% 1.55/0.59    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.55/0.59    inference(negated_conjecture,[],[f11])).
% 1.55/0.59  fof(f11,conjecture,(
% 1.55/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.55/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.55/0.59  fof(f40,plain,(
% 1.55/0.59    spl3_1),
% 1.55/0.59    inference(avatar_split_clause,[],[f19,f37])).
% 1.55/0.59  fof(f19,plain,(
% 1.55/0.59    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.55/0.59    inference(cnf_transformation,[],[f17])).
% 1.55/0.59  % SZS output end Proof for theBenchmark
% 1.55/0.59  % (28995)------------------------------
% 1.55/0.59  % (28995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (28995)Termination reason: Refutation
% 1.55/0.59  
% 1.55/0.59  % (28995)Memory used [KB]: 8187
% 1.55/0.59  % (28995)Time elapsed: 0.142 s
% 1.55/0.59  % (28995)------------------------------
% 1.55/0.59  % (28995)------------------------------
% 1.55/0.59  % (28987)Success in time 0.233 s
%------------------------------------------------------------------------------
