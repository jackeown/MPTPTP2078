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
% DateTime   : Thu Dec  3 12:32:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 330 expanded)
%              Number of leaves         :   38 ( 151 expanded)
%              Depth                    :   11
%              Number of atoms          :  466 ( 883 expanded)
%              Number of equality atoms :  103 ( 251 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f704,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f71,f75,f83,f87,f121,f157,f169,f181,f193,f204,f266,f303,f363,f437,f496,f533,f574,f631,f641,f701])).

fof(f701,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(avatar_contradiction_clause,[],[f700])).

fof(f700,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f36,f699])).

fof(f699,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f698,f642])).

fof(f642,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_39 ),
    inference(superposition,[],[f495,f62])).

fof(f62,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f495,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl3_39
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f698,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f697,f175])).

fof(f175,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_17
    | ~ spl3_18 ),
    inference(forward_demodulation,[],[f171,f163])).

fof(f163,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f159,f62])).

fof(f159,plain,
    ( k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_17 ),
    inference(superposition,[],[f82,f156])).

fof(f156,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_17
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f82,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f171,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)
    | ~ spl3_12
    | ~ spl3_18 ),
    inference(superposition,[],[f82,f168])).

fof(f168,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f697,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl3_7
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f696,f62])).

fof(f696,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_7
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(trivial_inequality_removal,[],[f695])).

fof(f695,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_7
    | ~ spl3_18
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f694,f168])).

fof(f694,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK1)
    | ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | ~ spl3_7
    | spl3_19
    | ~ spl3_39
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f667,f642])).

fof(f667,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | spl3_19
    | ~ spl3_44 ),
    inference(superposition,[],[f180,f640])).

fof(f640,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k5_xboole_0(X0,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X0,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f639])).

fof(f639,plain,
    ( spl3_44
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(k5_xboole_0(X0,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X0,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f180,plain,
    ( k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f36,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f641,plain,
    ( spl3_44
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f632,f629,f572,f531,f301,f264,f202,f191,f119,f81,f53,f639])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f119,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f191,plain,
    ( spl3_21
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f202,plain,
    ( spl3_22
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f264,plain,
    ( spl3_27
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f301,plain,
    ( spl3_30
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f531,plain,
    ( spl3_40
  <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X2),X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f572,plain,
    ( spl3_41
  <=> ! [X3,X5,X4] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f629,plain,
    ( spl3_42
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f632,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k5_xboole_0(X0,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X0,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_40
    | ~ spl3_41
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f630,f619])).

fof(f619,plain,
    ( ! [X8,X9] : k4_xboole_0(X8,X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f618,f315])).

fof(f315,plain,
    ( ! [X8] : k2_xboole_0(X8,k1_xboole_0) = X8
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f314,f54])).

fof(f54,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f314,plain,
    ( ! [X8] : k4_xboole_0(X8,k1_xboole_0) = k2_xboole_0(X8,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f308,f207])).

fof(f207,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(superposition,[],[f82,f203])).

fof(f203,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f308,plain,
    ( ! [X8] : k4_xboole_0(X8,k1_xboole_0) = k5_xboole_0(X8,k1_xboole_0)
    | ~ spl3_21
    | ~ spl3_30 ),
    inference(superposition,[],[f302,f192])).

fof(f192,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f302,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f301])).

fof(f618,plain,
    ( ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f617,f207])).

fof(f617,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_40
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f616,f565])).

fof(f565,plain,
    ( ! [X8,X9] : k4_xboole_0(k2_xboole_0(k1_xboole_0,X8),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_30
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f564,f315])).

fof(f564,plain,
    ( ! [X8,X9] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k2_xboole_0(X9,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X8),X9)
    | ~ spl3_22
    | ~ spl3_27
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f543,f265])).

fof(f265,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f264])).

fof(f543,plain,
    ( ! [X8,X9] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k2_xboole_0(X9,k1_xboole_0))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X8),X9)
    | ~ spl3_22
    | ~ spl3_40 ),
    inference(superposition,[],[f532,f203])).

fof(f532,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X2),X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k2_xboole_0(X1,X0)))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f531])).

fof(f616,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X9) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X8),X9)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_22
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f585,f216])).

fof(f216,plain,
    ( ! [X6,X7] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k2_xboole_0(k1_xboole_0,X7))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X6),X7)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f211,f111])).

fof(f111,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f82,f54])).

fof(f211,plain,
    ( ! [X6,X7] : k4_xboole_0(k5_xboole_0(k1_xboole_0,X6),X7) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k2_xboole_0(k1_xboole_0,X7)))
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(superposition,[],[f120,f203])).

fof(f120,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f119])).

fof(f585,plain,
    ( ! [X8,X9] : k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k2_xboole_0(k1_xboole_0,X9)))
    | ~ spl3_22
    | ~ spl3_41 ),
    inference(superposition,[],[f573,f203])).

fof(f573,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f572])).

fof(f630,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f629])).

fof(f631,plain,
    ( spl3_42
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f125,f119,f73,f629])).

fof(f73,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f125,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2)))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(superposition,[],[f120,f74])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f73])).

fof(f574,plain,
    ( spl3_41
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f130,f119,f61,f572])).

fof(f130,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f120,f62])).

fof(f533,plain,
    ( spl3_40
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f126,f119,f61,f531])).

fof(f126,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X2),X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k2_xboole_0(X1,X0)))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f120,f62])).

fof(f496,plain,
    ( spl3_39
    | ~ spl3_1
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f438,f435,f34,f493])).

fof(f435,plain,
    ( spl3_36
  <=> ! [X1,X2] :
        ( k2_xboole_0(X2,X1) = X2
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f438,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_36 ),
    inference(unit_resulting_resolution,[],[f36,f436])).

fof(f436,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = X2
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f435])).

fof(f437,plain,
    ( spl3_36
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f365,f361,f301,f202,f191,f81,f53,f435])).

fof(f361,plain,
    ( spl3_34
  <=> ! [X1,X2] :
        ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f365,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = X2
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_21
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f364,f315])).

fof(f364,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_12
    | ~ spl3_22
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f362,f207])).

fof(f362,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f361])).

fof(f363,plain,
    ( spl3_34
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f112,f81,f73,f361])).

fof(f112,plain,
    ( ! [X2,X1] :
        ( k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(superposition,[],[f82,f74])).

fof(f303,plain,
    ( spl3_30
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f116,f85,f57,f301])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f85,plain,
    ( spl3_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f116,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(superposition,[],[f86,f58])).

fof(f58,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f86,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f85])).

fof(f266,plain,
    ( spl3_27
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f111,f81,f53,f264])).

fof(f204,plain,
    ( spl3_22
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f100,f73,f49,f202])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f100,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f50,f74])).

fof(f50,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f193,plain,
    ( spl3_21
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f90,f65,f49,f191])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f90,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f50,f66])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f181,plain,
    ( ~ spl3_19
    | spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f95,f69,f44,f178])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f69,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f95,plain,
    ( k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | spl3_3
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f46,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f69])).

fof(f46,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f169,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f99,f73,f39,f166])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f99,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f41,f74])).

fof(f41,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f157,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f98,f73,f34,f154])).

fof(f98,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f36,f74])).

fof(f121,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f32,f119])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f87,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f28,f85])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f83,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f27,f81])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f75,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f71,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f65])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f61])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK2,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK2,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f34])).

fof(f19,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:39:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (27315)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (27306)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (27303)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (27314)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (27316)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (27313)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (27307)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (27304)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (27312)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (27302)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (27310)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (27309)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (27306)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f704,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f63,f67,f71,f75,f83,f87,f121,f157,f169,f181,f193,f204,f266,f303,f363,f437,f496,f533,f574,f631,f641,f701])).
% 0.21/0.49  fof(f701,plain,(
% 0.21/0.49    ~spl3_1 | ~spl3_7 | ~spl3_12 | ~spl3_17 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f700])).
% 0.21/0.49  fof(f700,plain,(
% 0.21/0.49    $false | (~spl3_1 | ~spl3_7 | ~spl3_12 | ~spl3_17 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(subsumption_resolution,[],[f36,f699])).
% 0.21/0.49  fof(f699,plain,(
% 0.21/0.49    ~r1_tarski(sK0,sK1) | (~spl3_7 | ~spl3_12 | ~spl3_17 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(forward_demodulation,[],[f698,f642])).
% 0.21/0.49  fof(f642,plain,(
% 0.21/0.49    sK1 = k2_xboole_0(sK0,sK1) | (~spl3_7 | ~spl3_39)),
% 0.21/0.49    inference(superposition,[],[f495,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f61])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f495,plain,(
% 0.21/0.49    sK1 = k2_xboole_0(sK1,sK0) | ~spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f493])).
% 0.21/0.49  fof(f493,plain,(
% 0.21/0.49    spl3_39 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f698,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | (~spl3_7 | ~spl3_12 | ~spl3_17 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(forward_demodulation,[],[f697,f175])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK2) | (~spl3_7 | ~spl3_12 | ~spl3_17 | ~spl3_18)),
% 0.21/0.49    inference(forward_demodulation,[],[f171,f163])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK0,sK1) | (~spl3_7 | ~spl3_12 | ~spl3_17)),
% 0.21/0.49    inference(forward_demodulation,[],[f159,f62])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    k2_xboole_0(sK1,sK0) = k5_xboole_0(sK1,k1_xboole_0) | (~spl3_12 | ~spl3_17)),
% 0.21/0.49    inference(superposition,[],[f82,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f154])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    spl3_17 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f81])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) | (~spl3_12 | ~spl3_18)),
% 0.21/0.49    inference(superposition,[],[f82,f168])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f166])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    spl3_18 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f697,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) | (~spl3_7 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(forward_demodulation,[],[f696,f62])).
% 0.21/0.49  fof(f696,plain,(
% 0.21/0.49    ~r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | (~spl3_7 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f695])).
% 0.21/0.49  fof(f695,plain,(
% 0.21/0.49    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | (~spl3_7 | ~spl3_18 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(forward_demodulation,[],[f694,f168])).
% 0.21/0.49  fof(f694,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK2,sK1) | ~r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | (~spl3_7 | spl3_19 | ~spl3_39 | ~spl3_44)),
% 0.21/0.49    inference(forward_demodulation,[],[f667,f642])).
% 0.21/0.49  fof(f667,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) | ~r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | (spl3_19 | ~spl3_44)),
% 0.21/0.49    inference(superposition,[],[f180,f640])).
% 0.21/0.49  fof(f640,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f639])).
% 0.21/0.49  fof(f639,plain,(
% 0.21/0.49    spl3_44 <=> ! [X1,X0,X2] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) | spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f178])).
% 0.21/0.49  fof(f178,plain,(
% 0.21/0.49    spl3_19 <=> k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f641,plain,(
% 0.21/0.49    spl3_44 | ~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_21 | ~spl3_22 | ~spl3_27 | ~spl3_30 | ~spl3_40 | ~spl3_41 | ~spl3_42),
% 0.21/0.49    inference(avatar_split_clause,[],[f632,f629,f572,f531,f301,f264,f202,f191,f119,f81,f53,f639])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl3_21 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    spl3_22 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    spl3_27 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl3_30 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.49  fof(f531,plain,(
% 0.21/0.49    spl3_40 <=> ! [X1,X0,X2] : k4_xboole_0(k5_xboole_0(X0,X2),X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k2_xboole_0(X1,X0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.49  fof(f572,plain,(
% 0.21/0.49    spl3_41 <=> ! [X3,X5,X4] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.49  fof(f629,plain,(
% 0.21/0.49    spl3_42 <=> ! [X1,X0,X2] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.49  fof(f632,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k4_xboole_0(X1,k2_xboole_0(X0,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | (~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_21 | ~spl3_22 | ~spl3_27 | ~spl3_30 | ~spl3_40 | ~spl3_41 | ~spl3_42)),
% 0.21/0.49    inference(forward_demodulation,[],[f630,f619])).
% 0.21/0.49  fof(f619,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))) ) | (~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_21 | ~spl3_22 | ~spl3_27 | ~spl3_30 | ~spl3_40 | ~spl3_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f618,f315])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    ( ! [X8] : (k2_xboole_0(X8,k1_xboole_0) = X8) ) | (~spl3_5 | ~spl3_12 | ~spl3_21 | ~spl3_22 | ~spl3_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f314,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ( ! [X8] : (k4_xboole_0(X8,k1_xboole_0) = k2_xboole_0(X8,k1_xboole_0)) ) | (~spl3_12 | ~spl3_21 | ~spl3_22 | ~spl3_30)),
% 0.21/0.49    inference(forward_demodulation,[],[f308,f207])).
% 0.21/0.49  fof(f207,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) ) | (~spl3_12 | ~spl3_22)),
% 0.21/0.49    inference(superposition,[],[f82,f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl3_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f202])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    ( ! [X8] : (k4_xboole_0(X8,k1_xboole_0) = k5_xboole_0(X8,k1_xboole_0)) ) | (~spl3_21 | ~spl3_30)),
% 0.21/0.49    inference(superposition,[],[f302,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | ~spl3_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f191])).
% 0.21/0.49  fof(f302,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | ~spl3_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f301])).
% 0.21/0.49  fof(f618,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,k1_xboole_0),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))) ) | (~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_21 | ~spl3_22 | ~spl3_27 | ~spl3_30 | ~spl3_40 | ~spl3_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f617,f207])).
% 0.21/0.49  fof(f617,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))) ) | (~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_21 | ~spl3_22 | ~spl3_27 | ~spl3_30 | ~spl3_40 | ~spl3_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f616,f565])).
% 0.21/0.49  fof(f565,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(k1_xboole_0,X8),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,X9))) ) | (~spl3_5 | ~spl3_12 | ~spl3_21 | ~spl3_22 | ~spl3_27 | ~spl3_30 | ~spl3_40)),
% 0.21/0.49    inference(forward_demodulation,[],[f564,f315])).
% 0.21/0.49  fof(f564,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k2_xboole_0(X9,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X8),X9)) ) | (~spl3_22 | ~spl3_27 | ~spl3_40)),
% 0.21/0.49    inference(forward_demodulation,[],[f543,f265])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) ) | ~spl3_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f264])).
% 0.21/0.49  fof(f543,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k2_xboole_0(X9,k1_xboole_0))) = k4_xboole_0(k5_xboole_0(k1_xboole_0,X8),X9)) ) | (~spl3_22 | ~spl3_40)),
% 0.21/0.49    inference(superposition,[],[f532,f203])).
% 0.21/0.49  fof(f532,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X2),X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k2_xboole_0(X1,X0)))) ) | ~spl3_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f531])).
% 0.21/0.49  fof(f616,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X9) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X8),X9)) ) | (~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_22 | ~spl3_41)),
% 0.21/0.49    inference(forward_demodulation,[],[f585,f216])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ( ! [X6,X7] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k2_xboole_0(k1_xboole_0,X7))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X6),X7)) ) | (~spl3_5 | ~spl3_12 | ~spl3_14 | ~spl3_22)),
% 0.21/0.49    inference(forward_demodulation,[],[f211,f111])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,X0)) ) | (~spl3_5 | ~spl3_12)),
% 0.21/0.49    inference(superposition,[],[f82,f54])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X6,X7] : (k4_xboole_0(k5_xboole_0(k1_xboole_0,X6),X7) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X6,k2_xboole_0(k1_xboole_0,X7)))) ) | (~spl3_14 | ~spl3_22)),
% 0.21/0.49    inference(superposition,[],[f120,f203])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f119])).
% 0.21/0.49  fof(f585,plain,(
% 0.21/0.49    ( ! [X8,X9] : (k4_xboole_0(k5_xboole_0(X8,k1_xboole_0),X9) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k2_xboole_0(k1_xboole_0,X9)))) ) | (~spl3_22 | ~spl3_41)),
% 0.21/0.49    inference(superposition,[],[f573,f203])).
% 0.21/0.49  fof(f573,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)) ) | ~spl3_41),
% 0.21/0.49    inference(avatar_component_clause,[],[f572])).
% 0.21/0.49  fof(f630,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | ~spl3_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f629])).
% 0.21/0.49  fof(f631,plain,(
% 0.21/0.49    spl3_42 | ~spl3_10 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f125,f119,f73,f629])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    spl3_10 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) ) | (~spl3_10 | ~spl3_14)),
% 0.21/0.49    inference(superposition,[],[f120,f74])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f73])).
% 0.21/0.49  fof(f574,plain,(
% 0.21/0.49    spl3_41 | ~spl3_7 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f130,f119,f61,f572])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X3,X5)),k4_xboole_0(X3,k2_xboole_0(X4,X5))) = k4_xboole_0(k5_xboole_0(X3,X4),X5)) ) | (~spl3_7 | ~spl3_14)),
% 0.21/0.49    inference(superposition,[],[f120,f62])).
% 0.21/0.49  fof(f533,plain,(
% 0.21/0.49    spl3_40 | ~spl3_7 | ~spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f126,f119,f61,f531])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X2),X1) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X2,X1)),k4_xboole_0(X2,k2_xboole_0(X1,X0)))) ) | (~spl3_7 | ~spl3_14)),
% 0.21/0.49    inference(superposition,[],[f120,f62])).
% 0.21/0.49  fof(f496,plain,(
% 0.21/0.49    spl3_39 | ~spl3_1 | ~spl3_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f438,f435,f34,f493])).
% 0.21/0.49  fof(f435,plain,(
% 0.21/0.49    spl3_36 <=> ! [X1,X2] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.49  fof(f438,plain,(
% 0.21/0.49    sK1 = k2_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_36)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f36,f436])).
% 0.21/0.49  fof(f436,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) ) | ~spl3_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f435])).
% 0.21/0.49  fof(f437,plain,(
% 0.21/0.49    spl3_36 | ~spl3_5 | ~spl3_12 | ~spl3_21 | ~spl3_22 | ~spl3_30 | ~spl3_34),
% 0.21/0.49    inference(avatar_split_clause,[],[f365,f361,f301,f202,f191,f81,f53,f435])).
% 0.21/0.49  fof(f361,plain,(
% 0.21/0.49    spl3_34 <=> ! [X1,X2] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.49  fof(f365,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) ) | (~spl3_5 | ~spl3_12 | ~spl3_21 | ~spl3_22 | ~spl3_30 | ~spl3_34)),
% 0.21/0.49    inference(forward_demodulation,[],[f364,f315])).
% 0.21/0.49  fof(f364,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl3_12 | ~spl3_22 | ~spl3_34)),
% 0.21/0.49    inference(forward_demodulation,[],[f362,f207])).
% 0.21/0.49  fof(f362,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | ~spl3_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f361])).
% 0.21/0.49  fof(f363,plain,(
% 0.21/0.49    spl3_34 | ~spl3_10 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f81,f73,f361])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k5_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl3_10 | ~spl3_12)),
% 0.21/0.49    inference(superposition,[],[f82,f74])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    spl3_30 | ~spl3_6 | ~spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f116,f85,f57,f301])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl3_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k5_xboole_0(X2,k3_xboole_0(X3,X2))) ) | (~spl3_6 | ~spl3_13)),
% 0.21/0.49    inference(superposition,[],[f86,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl3_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f85])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl3_27 | ~spl3_5 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f111,f81,f53,f264])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    spl3_22 | ~spl3_4 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f100,f73,f49,f202])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    spl3_4 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl3_4 | ~spl3_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f74])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl3_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f49])).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    spl3_21 | ~spl3_4 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f90,f65,f49,f191])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) ) | (~spl3_4 | ~spl3_8)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f50,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f65])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~spl3_19 | spl3_3 | ~spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f95,f69,f44,f178])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    spl3_3 <=> r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(k5_xboole_0(sK0,sK2),sK1) | (spl3_3 | ~spl3_9)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f46,f70])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f69])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f44])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    spl3_18 | ~spl3_2 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f99,f73,f39,f166])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f41,f74])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f39])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    spl3_17 | ~spl3_1 | ~spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f73,f34,f154])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_10)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f36,f74])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    spl3_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f119])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_xboole_1)).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f85])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f81])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f73])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.49    inference(nnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    spl3_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f69])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f65])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f61])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ~spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => (~r1_tarski(k5_xboole_0(sK0,sK2),sK1) & r1_tarski(sK2,sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.49    inference(negated_conjecture,[],[f11])).
% 0.21/0.49  fof(f11,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f39])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    r1_tarski(sK2,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f34])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    r1_tarski(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (27306)------------------------------
% 0.21/0.49  % (27306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27306)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (27306)Memory used [KB]: 6780
% 0.21/0.49  % (27306)Time elapsed: 0.070 s
% 0.21/0.49  % (27306)------------------------------
% 0.21/0.49  % (27306)------------------------------
% 0.21/0.50  % (27300)Success in time 0.137 s
%------------------------------------------------------------------------------
