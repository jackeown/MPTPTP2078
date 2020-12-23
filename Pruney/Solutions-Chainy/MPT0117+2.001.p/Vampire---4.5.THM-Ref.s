%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:51 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 214 expanded)
%              Number of leaves         :   28 ( 102 expanded)
%              Depth                    :   10
%              Number of atoms          :  312 ( 551 expanded)
%              Number of equality atoms :   68 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1136,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f50,f54,f58,f70,f78,f82,f86,f129,f161,f173,f186,f203,f520,f592,f637,f928,f976,f1132,f1135])).

fof(f1135,plain,
    ( ~ spl3_2
    | ~ spl3_49
    | spl3_61 ),
    inference(avatar_contradiction_clause,[],[f1134])).

fof(f1134,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_49
    | spl3_61 ),
    inference(subsumption_resolution,[],[f44,f1133])).

fof(f1133,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl3_49
    | spl3_61 ),
    inference(forward_demodulation,[],[f1131,f975])).

fof(f975,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl3_49
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f1131,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f1129])).

fof(f1129,plain,
    ( spl3_61
  <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f44,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1132,plain,
    ( ~ spl3_61
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_19
    | spl3_20
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f675,f635,f183,f170,f158,f84,f68,f56,f1129])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( spl3_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f158,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f170,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f183,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f635,plain,
    ( spl3_41
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X1,k2_xboole_0(X0,X2)) = k4_xboole_0(k5_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f675,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_19
    | spl3_20
    | ~ spl3_41 ),
    inference(trivial_inequality_removal,[],[f674])).

fof(f674,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_18
    | ~ spl3_19
    | spl3_20
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f673,f160])).

fof(f160,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f673,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_19
    | spl3_20
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f672,f181])).

fof(f181,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f176,f57])).

fof(f57,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f176,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_12
    | ~ spl3_19 ),
    inference(superposition,[],[f85,f172])).

fof(f172,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f85,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f672,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl3_8
    | spl3_20
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f651,f69])).

fof(f69,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f651,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))
    | ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | spl3_20
    | ~ spl3_41 ),
    inference(superposition,[],[f185,f636])).

fof(f636,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X1,k2_xboole_0(X0,X2)) = k4_xboole_0(k5_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f635])).

fof(f185,plain,
    ( k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f976,plain,
    ( spl3_49
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f929,f925,f68,f973])).

fof(f925,plain,
    ( spl3_45
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f929,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_8
    | ~ spl3_45 ),
    inference(superposition,[],[f927,f69])).

fof(f927,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f925])).

fof(f928,plain,
    ( spl3_45
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f168,f158,f84,f56,f925])).

fof(f168,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f164,f57])).

fof(f164,plain,
    ( k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(superposition,[],[f85,f160])).

fof(f637,plain,
    ( spl3_41
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_37
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f593,f590,f518,f201,f127,f84,f56,f635])).

fof(f127,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f201,plain,
    ( spl3_22
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f518,plain,
    ( spl3_37
  <=> ! [X3,X5,X4] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f590,plain,
    ( spl3_39
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f593,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X1,k2_xboole_0(X0,X2)) = k4_xboole_0(k5_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_37
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f591,f563])).

fof(f563,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,X10) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X10))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f562,f57])).

fof(f562,plain,
    ( ! [X10,X9] : k4_xboole_0(k5_xboole_0(X9,k1_xboole_0),X10) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X10))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f531,f216])).

fof(f216,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X6))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f215,f57])).

fof(f215,plain,
    ( ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),X6) = k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X6))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f210,f214])).

fof(f214,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f207,f57])).

fof(f207,plain,
    ( ! [X1] : k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(superposition,[],[f85,f202])).

fof(f202,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f201])).

fof(f210,plain,
    ( ! [X6,X5] : k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),X6) = k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X6)),k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_22 ),
    inference(superposition,[],[f128,f202])).

fof(f128,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f127])).

fof(f531,plain,
    ( ! [X10,X9] : k4_xboole_0(k5_xboole_0(X9,k1_xboole_0),X10) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)))
    | ~ spl3_22
    | ~ spl3_37 ),
    inference(superposition,[],[f519,f202])).

fof(f519,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f518])).

fof(f591,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f590])).

fof(f592,plain,
    ( spl3_39
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f142,f127,f80,f68,f590])).

fof(f80,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f142,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X1,X0),X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f137,f69])).

fof(f137,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k5_xboole_0(X1,X0),X2) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X2)),k1_xboole_0)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_11
    | ~ spl3_16 ),
    inference(superposition,[],[f128,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f520,plain,
    ( spl3_37
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f138,f127,f68,f518])).

fof(f138,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)
    | ~ spl3_8
    | ~ spl3_16 ),
    inference(superposition,[],[f128,f69])).

fof(f203,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f105,f80,f52,f201])).

fof(f52,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f105,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f53,f81])).

fof(f53,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f186,plain,
    ( ~ spl3_20
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f102,f76,f47,f183])).

fof(f47,plain,
    ( spl3_3
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f76,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f102,plain,
    ( k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f49,f77])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f49,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f173,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f104,f80,f42,f170])).

fof(f104,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f44,f81])).

fof(f161,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f103,f80,f37,f158])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f103,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f39,f81])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f129,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f35,f127])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f86,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f29,f84])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f82,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f78,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f68])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f54,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f22,f42])).

fof(f22,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:17:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (4217)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (4215)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (4211)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (4221)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (4219)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (4228)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (4212)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (4218)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (4226)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.49  % (4214)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (4223)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (4227)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (4216)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (4220)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (4213)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (4222)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.23/0.51  % (4224)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.23/0.53  % (4225)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.40/0.54  % (4216)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f1136,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f40,f45,f50,f54,f58,f70,f78,f82,f86,f129,f161,f173,f186,f203,f520,f592,f637,f928,f976,f1132,f1135])).
% 1.40/0.54  fof(f1135,plain,(
% 1.40/0.54    ~spl3_2 | ~spl3_49 | spl3_61),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f1134])).
% 1.40/0.54  fof(f1134,plain,(
% 1.40/0.54    $false | (~spl3_2 | ~spl3_49 | spl3_61)),
% 1.40/0.54    inference(subsumption_resolution,[],[f44,f1133])).
% 1.40/0.54  fof(f1133,plain,(
% 1.40/0.54    ~r1_tarski(sK2,sK1) | (~spl3_49 | spl3_61)),
% 1.40/0.54    inference(forward_demodulation,[],[f1131,f975])).
% 1.40/0.54  fof(f975,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_49),
% 1.40/0.54    inference(avatar_component_clause,[],[f973])).
% 1.40/0.54  fof(f973,plain,(
% 1.40/0.54    spl3_49 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.40/0.54  fof(f1131,plain,(
% 1.40/0.54    ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | spl3_61),
% 1.40/0.54    inference(avatar_component_clause,[],[f1129])).
% 1.40/0.54  fof(f1129,plain,(
% 1.40/0.54    spl3_61 <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    r1_tarski(sK2,sK1) | ~spl3_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f42])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    spl3_2 <=> r1_tarski(sK2,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.40/0.54  fof(f1132,plain,(
% 1.40/0.54    ~spl3_61 | ~spl3_5 | ~spl3_8 | ~spl3_12 | ~spl3_18 | ~spl3_19 | spl3_20 | ~spl3_41),
% 1.40/0.54    inference(avatar_split_clause,[],[f675,f635,f183,f170,f158,f84,f68,f56,f1129])).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    spl3_5 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    spl3_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.40/0.54  fof(f84,plain,(
% 1.40/0.54    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.40/0.54  fof(f158,plain,(
% 1.40/0.54    spl3_18 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.40/0.54  fof(f170,plain,(
% 1.40/0.54    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.40/0.54  fof(f183,plain,(
% 1.40/0.54    spl3_20 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.40/0.54  fof(f635,plain,(
% 1.40/0.54    spl3_41 <=> ! [X1,X0,X2] : (k4_xboole_0(X1,k2_xboole_0(X0,X2)) = k4_xboole_0(k5_xboole_0(X1,X0),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.40/0.54  fof(f675,plain,(
% 1.40/0.54    ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_5 | ~spl3_8 | ~spl3_12 | ~spl3_18 | ~spl3_19 | spl3_20 | ~spl3_41)),
% 1.40/0.54    inference(trivial_inequality_removal,[],[f674])).
% 1.40/0.54  fof(f674,plain,(
% 1.40/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_5 | ~spl3_8 | ~spl3_12 | ~spl3_18 | ~spl3_19 | spl3_20 | ~spl3_41)),
% 1.40/0.54    inference(forward_demodulation,[],[f673,f160])).
% 1.40/0.54  fof(f160,plain,(
% 1.40/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_18),
% 1.40/0.54    inference(avatar_component_clause,[],[f158])).
% 1.40/0.54  fof(f673,plain,(
% 1.40/0.54    k1_xboole_0 != k4_xboole_0(sK0,sK1) | ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_5 | ~spl3_8 | ~spl3_12 | ~spl3_19 | spl3_20 | ~spl3_41)),
% 1.40/0.54    inference(forward_demodulation,[],[f672,f181])).
% 1.40/0.54  fof(f181,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(sK1,sK2) | (~spl3_5 | ~spl3_12 | ~spl3_19)),
% 1.40/0.54    inference(forward_demodulation,[],[f176,f57])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 1.40/0.54    inference(avatar_component_clause,[],[f56])).
% 1.40/0.54  fof(f176,plain,(
% 1.40/0.54    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) | (~spl3_12 | ~spl3_19)),
% 1.40/0.54    inference(superposition,[],[f85,f172])).
% 1.40/0.54  fof(f172,plain,(
% 1.40/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_19),
% 1.40/0.54    inference(avatar_component_clause,[],[f170])).
% 1.40/0.54  fof(f85,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_12),
% 1.40/0.54    inference(avatar_component_clause,[],[f84])).
% 1.40/0.54  fof(f672,plain,(
% 1.40/0.54    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | (~spl3_8 | spl3_20 | ~spl3_41)),
% 1.40/0.54    inference(forward_demodulation,[],[f651,f69])).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_8),
% 1.40/0.54    inference(avatar_component_clause,[],[f68])).
% 1.40/0.54  fof(f651,plain,(
% 1.40/0.54    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) | ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | (spl3_20 | ~spl3_41)),
% 1.40/0.54    inference(superposition,[],[f185,f636])).
% 1.40/0.54  fof(f636,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k2_xboole_0(X0,X2)) = k4_xboole_0(k5_xboole_0(X1,X0),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_41),
% 1.40/0.54    inference(avatar_component_clause,[],[f635])).
% 1.40/0.54  fof(f185,plain,(
% 1.40/0.54    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) | spl3_20),
% 1.40/0.54    inference(avatar_component_clause,[],[f183])).
% 1.40/0.54  fof(f976,plain,(
% 1.40/0.54    spl3_49 | ~spl3_8 | ~spl3_45),
% 1.40/0.54    inference(avatar_split_clause,[],[f929,f925,f68,f973])).
% 1.40/0.54  fof(f925,plain,(
% 1.40/0.54    spl3_45 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 1.40/0.54  fof(f929,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(sK0,sK1) | (~spl3_8 | ~spl3_45)),
% 1.40/0.54    inference(superposition,[],[f927,f69])).
% 1.40/0.54  fof(f927,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_45),
% 1.40/0.54    inference(avatar_component_clause,[],[f925])).
% 1.40/0.54  fof(f928,plain,(
% 1.40/0.54    spl3_45 | ~spl3_5 | ~spl3_12 | ~spl3_18),
% 1.40/0.54    inference(avatar_split_clause,[],[f168,f158,f84,f56,f925])).
% 1.40/0.54  fof(f168,plain,(
% 1.40/0.54    sK1 = k2_xboole_0(sK1,sK0) | (~spl3_5 | ~spl3_12 | ~spl3_18)),
% 1.40/0.54    inference(forward_demodulation,[],[f164,f57])).
% 1.40/0.54  fof(f164,plain,(
% 1.40/0.54    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0) | (~spl3_12 | ~spl3_18)),
% 1.40/0.54    inference(superposition,[],[f85,f160])).
% 1.40/0.54  fof(f637,plain,(
% 1.40/0.54    spl3_41 | ~spl3_5 | ~spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_37 | ~spl3_39),
% 1.40/0.54    inference(avatar_split_clause,[],[f593,f590,f518,f201,f127,f84,f56,f635])).
% 1.40/0.54  fof(f127,plain,(
% 1.40/0.54    spl3_16 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.40/0.54  fof(f201,plain,(
% 1.40/0.54    spl3_22 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.40/0.54  fof(f518,plain,(
% 1.40/0.54    spl3_37 <=> ! [X3,X5,X4] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.40/0.54  fof(f590,plain,(
% 1.40/0.54    spl3_39 <=> ! [X1,X0,X2] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X1,X0),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.40/0.54  fof(f593,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k2_xboole_0(X0,X2)) = k4_xboole_0(k5_xboole_0(X1,X0),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | (~spl3_5 | ~spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_37 | ~spl3_39)),
% 1.40/0.54    inference(forward_demodulation,[],[f591,f563])).
% 1.40/0.54  fof(f563,plain,(
% 1.40/0.54    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X10))) ) | (~spl3_5 | ~spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_37)),
% 1.40/0.54    inference(forward_demodulation,[],[f562,f57])).
% 1.40/0.54  fof(f562,plain,(
% 1.40/0.54    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X9,k1_xboole_0),X10) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,X10))) ) | (~spl3_5 | ~spl3_12 | ~spl3_16 | ~spl3_22 | ~spl3_37)),
% 1.40/0.54    inference(forward_demodulation,[],[f531,f216])).
% 1.40/0.54  fof(f216,plain,(
% 1.40/0.54    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X6))) ) | (~spl3_5 | ~spl3_12 | ~spl3_16 | ~spl3_22)),
% 1.40/0.54    inference(forward_demodulation,[],[f215,f57])).
% 1.40/0.54  fof(f215,plain,(
% 1.40/0.54    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),X6) = k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X6))) ) | (~spl3_5 | ~spl3_12 | ~spl3_16 | ~spl3_22)),
% 1.40/0.54    inference(forward_demodulation,[],[f210,f214])).
% 1.40/0.54  fof(f214,plain,(
% 1.40/0.54    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl3_5 | ~spl3_12 | ~spl3_22)),
% 1.40/0.54    inference(forward_demodulation,[],[f207,f57])).
% 1.40/0.54  fof(f207,plain,(
% 1.40/0.54    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = k2_xboole_0(X1,k1_xboole_0)) ) | (~spl3_12 | ~spl3_22)),
% 1.40/0.54    inference(superposition,[],[f85,f202])).
% 1.40/0.54  fof(f202,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_22),
% 1.40/0.54    inference(avatar_component_clause,[],[f201])).
% 1.40/0.54  fof(f210,plain,(
% 1.40/0.54    ( ! [X6,X5] : (k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),X6) = k2_xboole_0(k4_xboole_0(X5,k2_xboole_0(k1_xboole_0,X6)),k1_xboole_0)) ) | (~spl3_16 | ~spl3_22)),
% 1.40/0.54    inference(superposition,[],[f128,f202])).
% 1.40/0.54  fof(f128,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ) | ~spl3_16),
% 1.40/0.54    inference(avatar_component_clause,[],[f127])).
% 1.40/0.54  fof(f531,plain,(
% 1.40/0.54    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X9,k1_xboole_0),X10) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X9,k2_xboole_0(k1_xboole_0,X10)))) ) | (~spl3_22 | ~spl3_37)),
% 1.40/0.54    inference(superposition,[],[f519,f202])).
% 1.40/0.54  fof(f519,plain,(
% 1.40/0.54    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)) ) | ~spl3_37),
% 1.40/0.54    inference(avatar_component_clause,[],[f518])).
% 1.40/0.54  fof(f591,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X1,X0),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_39),
% 1.40/0.54    inference(avatar_component_clause,[],[f590])).
% 1.40/0.54  fof(f592,plain,(
% 1.40/0.54    spl3_39 | ~spl3_8 | ~spl3_11 | ~spl3_16),
% 1.40/0.54    inference(avatar_split_clause,[],[f142,f127,f80,f68,f590])).
% 1.40/0.54  fof(f80,plain,(
% 1.40/0.54    spl3_11 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.40/0.54  fof(f142,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k4_xboole_0(k5_xboole_0(X1,X0),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | (~spl3_8 | ~spl3_11 | ~spl3_16)),
% 1.40/0.54    inference(forward_demodulation,[],[f137,f69])).
% 1.40/0.54  fof(f137,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X2) = k2_xboole_0(k4_xboole_0(X1,k2_xboole_0(X0,X2)),k1_xboole_0) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | (~spl3_11 | ~spl3_16)),
% 1.40/0.54    inference(superposition,[],[f128,f81])).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 1.40/0.54    inference(avatar_component_clause,[],[f80])).
% 1.40/0.54  fof(f520,plain,(
% 1.40/0.54    spl3_37 | ~spl3_8 | ~spl3_16),
% 1.40/0.54    inference(avatar_split_clause,[],[f138,f127,f68,f518])).
% 1.40/0.54  fof(f138,plain,(
% 1.40/0.54    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)) ) | (~spl3_8 | ~spl3_16)),
% 1.40/0.54    inference(superposition,[],[f128,f69])).
% 1.40/0.54  fof(f203,plain,(
% 1.40/0.54    spl3_22 | ~spl3_4 | ~spl3_11),
% 1.40/0.54    inference(avatar_split_clause,[],[f105,f80,f52,f201])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    spl3_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.40/0.54  fof(f105,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl3_4 | ~spl3_11)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f53,f81])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_4),
% 1.40/0.54    inference(avatar_component_clause,[],[f52])).
% 1.40/0.54  fof(f186,plain,(
% 1.40/0.54    ~spl3_20 | spl3_3 | ~spl3_10),
% 1.40/0.54    inference(avatar_split_clause,[],[f102,f76,f47,f183])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    spl3_3 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.40/0.54  fof(f76,plain,(
% 1.40/0.54    spl3_10 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.40/0.54  fof(f102,plain,(
% 1.40/0.54    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) | (spl3_3 | ~spl3_10)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f49,f77])).
% 1.40/0.54  fof(f77,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_10),
% 1.40/0.54    inference(avatar_component_clause,[],[f76])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) | spl3_3),
% 1.40/0.54    inference(avatar_component_clause,[],[f47])).
% 1.40/0.54  fof(f173,plain,(
% 1.40/0.54    spl3_19 | ~spl3_2 | ~spl3_11),
% 1.40/0.54    inference(avatar_split_clause,[],[f104,f80,f42,f170])).
% 1.40/0.54  fof(f104,plain,(
% 1.40/0.54    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_11)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f44,f81])).
% 1.40/0.54  fof(f161,plain,(
% 1.40/0.54    spl3_18 | ~spl3_1 | ~spl3_11),
% 1.40/0.54    inference(avatar_split_clause,[],[f103,f80,f37,f158])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    spl3_1 <=> r1_tarski(sK0,sK1)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.40/0.54  fof(f103,plain,(
% 1.40/0.54    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_11)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f39,f81])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    r1_tarski(sK0,sK1) | ~spl3_1),
% 1.40/0.54    inference(avatar_component_clause,[],[f37])).
% 1.40/0.54  fof(f129,plain,(
% 1.40/0.54    spl3_16),
% 1.40/0.54    inference(avatar_split_clause,[],[f35,f127])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).
% 1.40/0.54  fof(f86,plain,(
% 1.40/0.54    spl3_12),
% 1.40/0.54    inference(avatar_split_clause,[],[f29,f84])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,axiom,(
% 1.40/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.40/0.54  fof(f82,plain,(
% 1.40/0.54    spl3_11),
% 1.40/0.54    inference(avatar_split_clause,[],[f34,f80])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.40/0.54    inference(nnf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.40/0.54  fof(f78,plain,(
% 1.40/0.54    spl3_10),
% 1.40/0.54    inference(avatar_split_clause,[],[f33,f76])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f20])).
% 1.40/0.54  fof(f70,plain,(
% 1.40/0.54    spl3_8),
% 1.40/0.54    inference(avatar_split_clause,[],[f28,f68])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    spl3_5),
% 1.40/0.54    inference(avatar_split_clause,[],[f25,f56])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,axiom,(
% 1.40/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.40/0.54  fof(f54,plain,(
% 1.40/0.54    spl3_4),
% 1.40/0.54    inference(avatar_split_clause,[],[f24,f52])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.54  fof(f50,plain,(
% 1.40/0.54    ~spl3_3),
% 1.40/0.54    inference(avatar_split_clause,[],[f23,f47])).
% 1.40/0.54  fof(f23,plain,(
% 1.40/0.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 1.40/0.54    inference(flattening,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 1.40/0.54    inference(ennf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,negated_conjecture,(
% 1.40/0.54    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.40/0.54    inference(negated_conjecture,[],[f12])).
% 1.40/0.54  fof(f12,conjecture,(
% 1.40/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    spl3_2),
% 1.40/0.54    inference(avatar_split_clause,[],[f22,f42])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    r1_tarski(sK2,sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    spl3_1),
% 1.40/0.54    inference(avatar_split_clause,[],[f21,f37])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    r1_tarski(sK0,sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (4216)------------------------------
% 1.40/0.54  % (4216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (4216)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (4216)Memory used [KB]: 7547
% 1.40/0.54  % (4216)Time elapsed: 0.134 s
% 1.40/0.54  % (4216)------------------------------
% 1.40/0.54  % (4216)------------------------------
% 1.40/0.56  % (4210)Success in time 0.201 s
%------------------------------------------------------------------------------
