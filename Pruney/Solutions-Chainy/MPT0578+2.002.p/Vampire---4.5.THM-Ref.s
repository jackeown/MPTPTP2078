%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 199 expanded)
%              Number of leaves         :   32 (  95 expanded)
%              Depth                    :    6
%              Number of atoms          :  325 ( 535 expanded)
%              Number of equality atoms :   58 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3665,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f50,f54,f58,f62,f66,f70,f74,f80,f88,f134,f252,f446,f477,f503,f514,f752,f1027,f3198,f3648,f3664])).

fof(f3664,plain,
    ( spl2_1
    | ~ spl2_8
    | ~ spl2_529
    | ~ spl2_590 ),
    inference(avatar_contradiction_clause,[],[f3663])).

fof(f3663,plain,
    ( $false
    | spl2_1
    | ~ spl2_8
    | ~ spl2_529
    | ~ spl2_590 ),
    inference(subsumption_resolution,[],[f3662,f35])).

fof(f35,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_1
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3662,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))
    | ~ spl2_8
    | ~ spl2_529
    | ~ spl2_590 ),
    inference(forward_demodulation,[],[f3651,f3197])).

fof(f3197,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_529 ),
    inference(avatar_component_clause,[],[f3195])).

fof(f3195,plain,
    ( spl2_529
  <=> k10_relat_1(sK0,k1_relat_1(sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_529])])).

fof(f3651,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_8
    | ~ spl2_590 ),
    inference(resolution,[],[f3647,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f3647,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_590 ),
    inference(avatar_component_clause,[],[f3645])).

fof(f3645,plain,
    ( spl2_590
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_590])])).

fof(f3648,plain,
    ( spl2_590
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_171 ),
    inference(avatar_split_clause,[],[f3643,f1025,f56,f38,f3645])).

fof(f38,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f56,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1025,plain,
    ( spl2_171
  <=> ! [X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1))
        | ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).

fof(f3643,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_171 ),
    inference(subsumption_resolution,[],[f3641,f40])).

fof(f40,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f3641,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ v1_relat_1(sK1)
    | ~ spl2_6
    | ~ spl2_171 ),
    inference(resolution,[],[f1026,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f1026,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1)
        | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1)) )
    | ~ spl2_171 ),
    inference(avatar_component_clause,[],[f1025])).

fof(f3198,plain,
    ( spl2_529
    | ~ spl2_12
    | ~ spl2_85 ),
    inference(avatar_split_clause,[],[f3190,f501,f85,f3195])).

fof(f85,plain,
    ( spl2_12
  <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f501,plain,
    ( spl2_85
  <=> ! [X4] : k10_relat_1(sK0,k10_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k10_relat_1(sK1,X4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).

fof(f3190,plain,
    ( k10_relat_1(sK0,k1_relat_1(sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl2_12
    | ~ spl2_85 ),
    inference(superposition,[],[f502,f87])).

fof(f87,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f85])).

fof(f502,plain,
    ( ! [X4] : k10_relat_1(sK0,k10_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k10_relat_1(sK1,X4)))
    | ~ spl2_85 ),
    inference(avatar_component_clause,[],[f501])).

fof(f1027,plain,
    ( spl2_171
    | ~ spl2_20
    | ~ spl2_127 ),
    inference(avatar_split_clause,[],[f1003,f748,f132,f1025])).

fof(f132,plain,
    ( spl2_20
  <=> ! [X3,X2] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f748,plain,
    ( spl2_127
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_127])])).

fof(f1003,plain,
    ( ! [X1] :
        ( r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1))
        | ~ r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1) )
    | ~ spl2_20
    | ~ spl2_127 ),
    inference(superposition,[],[f133,f750])).

fof(f750,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl2_127 ),
    inference(avatar_component_clause,[],[f748])).

fof(f133,plain,
    ( ! [X2,X3] :
        ( r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3))
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f752,plain,
    ( spl2_127
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f745,f511,f444,f748])).

fof(f444,plain,
    ( spl2_75
  <=> ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f511,plain,
    ( spl2_87
  <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f745,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl2_75
    | ~ spl2_87 ),
    inference(superposition,[],[f445,f513])).

fof(f513,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f511])).

fof(f445,plain,
    ( ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0)
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f444])).

fof(f514,plain,
    ( spl2_87
    | ~ spl2_4
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f483,f467,f48,f511])).

fof(f48,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f467,plain,
    ( spl2_80
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f483,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl2_4
    | ~ spl2_80 ),
    inference(resolution,[],[f468,f49])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f468,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f467])).

fof(f503,plain,
    ( spl2_85
    | ~ spl2_11
    | ~ spl2_75
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f499,f467,f444,f78,f501])).

fof(f78,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k10_relat_1(X0,X1) = k3_xboole_0(k1_relat_1(X0),k10_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f499,plain,
    ( ! [X4] : k10_relat_1(sK0,k10_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k10_relat_1(sK1,X4)))
    | ~ spl2_11
    | ~ spl2_75
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f481,f445])).

fof(f481,plain,
    ( ! [X4] : k10_relat_1(k5_relat_1(sK0,sK1),X4) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(k5_relat_1(sK0,sK1),X4))
    | ~ spl2_11
    | ~ spl2_80 ),
    inference(resolution,[],[f468,f79])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k10_relat_1(X0,X1) = k3_xboole_0(k1_relat_1(X0),k10_relat_1(X0,X1)) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f78])).

fof(f477,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9
    | spl2_80 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_9
    | spl2_80 ),
    inference(subsumption_resolution,[],[f475,f45])).

fof(f45,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f475,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_2
    | ~ spl2_9
    | spl2_80 ),
    inference(subsumption_resolution,[],[f474,f40])).

fof(f474,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_9
    | spl2_80 ),
    inference(resolution,[],[f469,f69])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( v1_relat_1(k5_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f469,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl2_80 ),
    inference(avatar_component_clause,[],[f467])).

fof(f446,plain,
    ( spl2_75
    | ~ spl2_2
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f438,f250,f38,f444])).

fof(f250,plain,
    ( spl2_42
  <=> ! [X3,X2] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f438,plain,
    ( ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0)
    | ~ spl2_2
    | ~ spl2_42 ),
    inference(resolution,[],[f251,f40])).

fof(f251,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)) )
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f250])).

fof(f252,plain,
    ( spl2_42
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f243,f60,f43,f250])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f243,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f61,f45])).

fof(f61,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f134,plain,
    ( spl2_20
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f125,f72,f43,f132])).

fof(f72,plain,
    ( spl2_10
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f125,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X2,X3)
        | r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) )
    | ~ spl2_3
    | ~ spl2_10 ),
    inference(resolution,[],[f73,f45])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | ~ r1_tarski(X0,X1)
        | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f88,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f81,f48,f38,f85])).

fof(f81,plain,
    ( k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f49,f40])).

fof(f80,plain,
    ( spl2_11
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f76,f64,f56,f52,f78])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X0,X1) = k3_xboole_0(k1_relat_1(X0),k10_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f75,f53])).

fof(f53,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( k10_relat_1(X0,X1) = k3_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(resolution,[],[f65,f57])).

fof(f74,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f70,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f66,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f29,f64])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f62,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f28,f60])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

fof(f58,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f27,f56])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f52])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f25,f48])).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f46,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1))
        & v1_relat_1(X1) )
   => ( k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f23,f38])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f33])).

fof(f24,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:07:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (9277)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.42  % (9278)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (9283)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.44  % (9279)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (9280)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.45  % (9275)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.45  % (9274)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.45  % (9276)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.46  % (9272)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.47  % (9273)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.47  % (9281)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.48  % (9282)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.49  % (9277)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f3665,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f36,f41,f46,f50,f54,f58,f62,f66,f70,f74,f80,f88,f134,f252,f446,f477,f503,f514,f752,f1027,f3198,f3648,f3664])).
% 0.22/0.49  fof(f3664,plain,(
% 0.22/0.49    spl2_1 | ~spl2_8 | ~spl2_529 | ~spl2_590),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f3663])).
% 0.22/0.49  fof(f3663,plain,(
% 0.22/0.49    $false | (spl2_1 | ~spl2_8 | ~spl2_529 | ~spl2_590)),
% 0.22/0.49    inference(subsumption_resolution,[],[f3662,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) | spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    spl2_1 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f3662,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) | (~spl2_8 | ~spl2_529 | ~spl2_590)),
% 0.22/0.49    inference(forward_demodulation,[],[f3651,f3197])).
% 0.22/0.49  fof(f3197,plain,(
% 0.22/0.49    k10_relat_1(sK0,k1_relat_1(sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl2_529),
% 0.22/0.49    inference(avatar_component_clause,[],[f3195])).
% 0.22/0.49  fof(f3195,plain,(
% 0.22/0.49    spl2_529 <=> k10_relat_1(sK0,k1_relat_1(sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_529])])).
% 0.22/0.49  fof(f3651,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | (~spl2_8 | ~spl2_590)),
% 0.22/0.49    inference(resolution,[],[f3647,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl2_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.49  fof(f3647,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | ~spl2_590),
% 0.22/0.49    inference(avatar_component_clause,[],[f3645])).
% 0.22/0.49  fof(f3645,plain,(
% 0.22/0.49    spl2_590 <=> r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_590])])).
% 0.22/0.49  fof(f3648,plain,(
% 0.22/0.49    spl2_590 | ~spl2_2 | ~spl2_6 | ~spl2_171),
% 0.22/0.49    inference(avatar_split_clause,[],[f3643,f1025,f56,f38,f3645])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl2_6 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f1025,plain,(
% 0.22/0.49    spl2_171 <=> ! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1)) | ~r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_171])])).
% 0.22/0.49  fof(f3643,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | (~spl2_2 | ~spl2_6 | ~spl2_171)),
% 0.22/0.49    inference(subsumption_resolution,[],[f3641,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f38])).
% 0.22/0.49  fof(f3641,plain,(
% 0.22/0.49    r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | ~v1_relat_1(sK1) | (~spl2_6 | ~spl2_171)),
% 0.22/0.49    inference(resolution,[],[f1026,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f1026,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1) | r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1))) ) | ~spl2_171),
% 0.22/0.49    inference(avatar_component_clause,[],[f1025])).
% 0.22/0.49  fof(f3198,plain,(
% 0.22/0.49    spl2_529 | ~spl2_12 | ~spl2_85),
% 0.22/0.49    inference(avatar_split_clause,[],[f3190,f501,f85,f3195])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl2_12 <=> k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.49  fof(f501,plain,(
% 0.22/0.49    spl2_85 <=> ! [X4] : k10_relat_1(sK0,k10_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k10_relat_1(sK1,X4)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_85])])).
% 0.22/0.49  fof(f3190,plain,(
% 0.22/0.49    k10_relat_1(sK0,k1_relat_1(sK1)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k1_relat_1(sK1))) | (~spl2_12 | ~spl2_85)),
% 0.22/0.49    inference(superposition,[],[f502,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | ~spl2_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f502,plain,(
% 0.22/0.49    ( ! [X4] : (k10_relat_1(sK0,k10_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k10_relat_1(sK1,X4)))) ) | ~spl2_85),
% 0.22/0.49    inference(avatar_component_clause,[],[f501])).
% 0.22/0.49  fof(f1027,plain,(
% 0.22/0.49    spl2_171 | ~spl2_20 | ~spl2_127),
% 0.22/0.49    inference(avatar_split_clause,[],[f1003,f748,f132,f1025])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    spl2_20 <=> ! [X3,X2] : (~r1_tarski(X2,X3) | r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.49  fof(f748,plain,(
% 0.22/0.49    spl2_127 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_127])])).
% 0.22/0.49  fof(f1003,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,X1)) | ~r1_tarski(k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1))),X1)) ) | (~spl2_20 | ~spl2_127)),
% 0.22/0.49    inference(superposition,[],[f133,f750])).
% 0.22/0.49  fof(f750,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) | ~spl2_127),
% 0.22/0.49    inference(avatar_component_clause,[],[f748])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3)) | ~r1_tarski(X2,X3)) ) | ~spl2_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f132])).
% 0.22/0.49  fof(f752,plain,(
% 0.22/0.49    spl2_127 | ~spl2_75 | ~spl2_87),
% 0.22/0.49    inference(avatar_split_clause,[],[f745,f511,f444,f748])).
% 0.22/0.49  fof(f444,plain,(
% 0.22/0.49    spl2_75 <=> ! [X0] : k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 0.22/0.49  fof(f511,plain,(
% 0.22/0.49    spl2_87 <=> k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 0.22/0.49  fof(f745,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k10_relat_1(sK1,k2_relat_1(k5_relat_1(sK0,sK1)))) | (~spl2_75 | ~spl2_87)),
% 0.22/0.49    inference(superposition,[],[f445,f513])).
% 0.22/0.49  fof(f513,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) | ~spl2_87),
% 0.22/0.49    inference(avatar_component_clause,[],[f511])).
% 0.22/0.49  fof(f445,plain,(
% 0.22/0.49    ( ! [X0] : (k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0)) ) | ~spl2_75),
% 0.22/0.49    inference(avatar_component_clause,[],[f444])).
% 0.22/0.49  fof(f514,plain,(
% 0.22/0.49    spl2_87 | ~spl2_4 | ~spl2_80),
% 0.22/0.49    inference(avatar_split_clause,[],[f483,f467,f48,f511])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    spl2_4 <=> ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f467,plain,(
% 0.22/0.49    spl2_80 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 0.22/0.49  fof(f483,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(k5_relat_1(sK0,sK1),k2_relat_1(k5_relat_1(sK0,sK1))) | (~spl2_4 | ~spl2_80)),
% 0.22/0.49    inference(resolution,[],[f468,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) ) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f48])).
% 0.22/0.49  fof(f468,plain,(
% 0.22/0.49    v1_relat_1(k5_relat_1(sK0,sK1)) | ~spl2_80),
% 0.22/0.49    inference(avatar_component_clause,[],[f467])).
% 0.22/0.49  fof(f503,plain,(
% 0.22/0.49    spl2_85 | ~spl2_11 | ~spl2_75 | ~spl2_80),
% 0.22/0.49    inference(avatar_split_clause,[],[f499,f467,f444,f78,f501])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl2_11 <=> ! [X1,X0] : (k10_relat_1(X0,X1) = k3_xboole_0(k1_relat_1(X0),k10_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.49  fof(f499,plain,(
% 0.22/0.49    ( ! [X4] : (k10_relat_1(sK0,k10_relat_1(sK1,X4)) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(sK0,k10_relat_1(sK1,X4)))) ) | (~spl2_11 | ~spl2_75 | ~spl2_80)),
% 0.22/0.49    inference(forward_demodulation,[],[f481,f445])).
% 0.22/0.49  fof(f481,plain,(
% 0.22/0.49    ( ! [X4] : (k10_relat_1(k5_relat_1(sK0,sK1),X4) = k3_xboole_0(k1_relat_1(k5_relat_1(sK0,sK1)),k10_relat_1(k5_relat_1(sK0,sK1),X4))) ) | (~spl2_11 | ~spl2_80)),
% 0.22/0.49    inference(resolution,[],[f468,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(X0,X1) = k3_xboole_0(k1_relat_1(X0),k10_relat_1(X0,X1))) ) | ~spl2_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f78])).
% 0.22/0.49  fof(f477,plain,(
% 0.22/0.49    ~spl2_2 | ~spl2_3 | ~spl2_9 | spl2_80),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f476])).
% 0.22/0.49  fof(f476,plain,(
% 0.22/0.49    $false | (~spl2_2 | ~spl2_3 | ~spl2_9 | spl2_80)),
% 0.22/0.49    inference(subsumption_resolution,[],[f475,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    v1_relat_1(sK0) | ~spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    spl2_3 <=> v1_relat_1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f475,plain,(
% 0.22/0.49    ~v1_relat_1(sK0) | (~spl2_2 | ~spl2_9 | spl2_80)),
% 0.22/0.49    inference(subsumption_resolution,[],[f474,f40])).
% 0.22/0.49  fof(f474,plain,(
% 0.22/0.49    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | (~spl2_9 | spl2_80)),
% 0.22/0.49    inference(resolution,[],[f469,f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl2_9 <=> ! [X1,X0] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.49  fof(f469,plain,(
% 0.22/0.49    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl2_80),
% 0.22/0.49    inference(avatar_component_clause,[],[f467])).
% 0.22/0.49  fof(f446,plain,(
% 0.22/0.49    spl2_75 | ~spl2_2 | ~spl2_42),
% 0.22/0.49    inference(avatar_split_clause,[],[f438,f250,f38,f444])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    spl2_42 <=> ! [X3,X2] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 0.22/0.49  fof(f438,plain,(
% 0.22/0.49    ( ! [X0] : (k10_relat_1(sK0,k10_relat_1(sK1,X0)) = k10_relat_1(k5_relat_1(sK0,sK1),X0)) ) | (~spl2_2 | ~spl2_42)),
% 0.22/0.49    inference(resolution,[],[f251,f40])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3))) ) | ~spl2_42),
% 0.22/0.49    inference(avatar_component_clause,[],[f250])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl2_42 | ~spl2_3 | ~spl2_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f243,f60,f43,f250])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl2_7 <=> ! [X1,X0,X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(sK0,X2),X3) = k10_relat_1(sK0,k10_relat_1(X2,X3))) ) | (~spl2_3 | ~spl2_7)),
% 0.22/0.49    inference(resolution,[],[f61,f45])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))) ) | ~spl2_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl2_20 | ~spl2_3 | ~spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f125,f72,f43,f132])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl2_10 <=> ! [X1,X0,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_tarski(k10_relat_1(sK0,X2),k10_relat_1(sK0,X3))) ) | (~spl2_3 | ~spl2_10)),
% 0.22/0.49    inference(resolution,[],[f73,f45])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(X0,X1) | r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) | ~spl2_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl2_12 | ~spl2_2 | ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f81,f48,f38,f85])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    k1_relat_1(sK1) = k10_relat_1(sK1,k2_relat_1(sK1)) | (~spl2_2 | ~spl2_4)),
% 0.22/0.49    inference(resolution,[],[f49,f40])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl2_11 | ~spl2_5 | ~spl2_6 | ~spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f76,f64,f56,f52,f78])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k3_xboole_0(k1_relat_1(X0),k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_6 | ~spl2_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f75,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f52])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k10_relat_1(X0,X1) = k3_xboole_0(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~v1_relat_1(X0)) ) | (~spl2_6 | ~spl2_8)),
% 0.22/0.49    inference(resolution,[],[f65,f57])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl2_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f72])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl2_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f68])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f64])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f60])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f56])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    spl2_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f26,f52])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f25,f48])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f22,f43])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ? [X1] : (k1_relat_1(k5_relat_1(sK0,X1)) != k10_relat_1(sK0,k1_relat_1(X1)) & v1_relat_1(X1)) => (k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_relat_1(k5_relat_1(X0,X1)) != k10_relat_1(X0,k1_relat_1(X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f38])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    v1_relat_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f24,f33])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    k1_relat_1(k5_relat_1(sK0,sK1)) != k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (9277)------------------------------
% 0.22/0.49  % (9277)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (9277)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (9277)Memory used [KB]: 13176
% 0.22/0.49  % (9277)Time elapsed: 0.079 s
% 0.22/0.49  % (9277)------------------------------
% 0.22/0.49  % (9277)------------------------------
% 0.22/0.50  % (9268)Success in time 0.136 s
%------------------------------------------------------------------------------
