%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 227 expanded)
%              Number of leaves         :   38 ( 109 expanded)
%              Depth                    :    7
%              Number of atoms          :  316 ( 533 expanded)
%              Number of equality atoms :   79 ( 138 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f67,f71,f75,f80,f84,f90,f95,f111,f119,f136,f151,f164,f179,f200,f214,f218,f260,f265,f298,f313,f320,f333,f648,f683])).

fof(f683,plain,
    ( ~ spl4_16
    | ~ spl4_21
    | ~ spl4_38
    | spl4_41
    | ~ spl4_56 ),
    inference(avatar_contradiction_clause,[],[f682])).

fof(f682,plain,
    ( $false
    | ~ spl4_16
    | ~ spl4_21
    | ~ spl4_38
    | spl4_41
    | ~ spl4_56 ),
    inference(subsumption_resolution,[],[f681,f135])).

fof(f135,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_16
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f681,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,sK2)
    | ~ spl4_21
    | ~ spl4_38
    | spl4_41
    | ~ spl4_56 ),
    inference(backward_demodulation,[],[f332,f680])).

fof(f680,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_21
    | ~ spl4_38
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f665,f312])).

fof(f312,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl4_38
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f665,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK0)
    | ~ spl4_21
    | ~ spl4_56 ),
    inference(superposition,[],[f647,f178])).

fof(f178,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_21
  <=> sK1 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f647,plain,
    ( ! [X16] : k4_xboole_0(sK2,k2_xboole_0(sK1,X16)) = k4_xboole_0(sK2,X16)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f646])).

fof(f646,plain,
    ( spl4_56
  <=> ! [X16] : k4_xboole_0(sK2,k2_xboole_0(sK1,X16)) = k4_xboole_0(sK2,X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f332,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | spl4_41 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl4_41
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f648,plain,
    ( spl4_56
    | ~ spl4_33
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f346,f310,f258,f646])).

fof(f258,plain,
    ( spl4_33
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f346,plain,
    ( ! [X16] : k4_xboole_0(sK2,k2_xboole_0(sK1,X16)) = k4_xboole_0(sK2,X16)
    | ~ spl4_33
    | ~ spl4_38 ),
    inference(superposition,[],[f259,f312])).

fof(f259,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f258])).

fof(f333,plain,
    ( ~ spl4_41
    | spl4_3
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f325,f318,f60,f330])).

fof(f60,plain,
    ( spl4_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f318,plain,
    ( spl4_39
  <=> ! [X3,X4] :
        ( k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4))
        | r1_xboole_0(X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f325,plain,
    ( k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | spl4_3
    | ~ spl4_39 ),
    inference(resolution,[],[f319,f62])).

fof(f62,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f319,plain,
    ( ! [X4,X3] :
        ( r1_xboole_0(X4,X3)
        | k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4)) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f318])).

fof(f320,plain,
    ( spl4_39
    | ~ spl4_8
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f231,f212,f82,f318])).

fof(f82,plain,
    ( spl4_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f212,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f231,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4))
        | r1_xboole_0(X4,X3) )
    | ~ spl4_8
    | ~ spl4_26 ),
    inference(resolution,[],[f213,f83])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f213,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f212])).

fof(f313,plain,
    ( spl4_38
    | ~ spl4_10
    | ~ spl4_25
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f303,f295,f198,f93,f310])).

fof(f93,plain,
    ( spl4_10
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f198,plain,
    ( spl4_25
  <=> ! [X3,X4] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f295,plain,
    ( spl4_37
  <=> k4_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f303,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl4_10
    | ~ spl4_25
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f299,f199])).

fof(f199,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f198])).

fof(f299,plain,
    ( k4_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl4_10
    | ~ spl4_37 ),
    inference(superposition,[],[f297,f94])).

fof(f94,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f93])).

fof(f297,plain,
    ( k4_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f295])).

fof(f298,plain,
    ( spl4_37
    | ~ spl4_4
    | ~ spl4_20
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f270,f262,f162,f65,f295])).

fof(f65,plain,
    ( spl4_4
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f162,plain,
    ( spl4_20
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f262,plain,
    ( spl4_34
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f270,plain,
    ( k4_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2)
    | ~ spl4_4
    | ~ spl4_20
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f267,f66])).

fof(f66,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f267,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl4_20
    | ~ spl4_34 ),
    inference(superposition,[],[f163,f264])).

fof(f264,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f262])).

fof(f163,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f162])).

fof(f265,plain,
    ( spl4_34
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f239,f216,f87,f262])).

fof(f87,plain,
    ( spl4_9
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f216,plain,
    ( spl4_27
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f239,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))
    | ~ spl4_9
    | ~ spl4_27 ),
    inference(resolution,[],[f217,f89])).

fof(f89,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f87])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f216])).

fof(f260,plain,(
    spl4_33 ),
    inference(avatar_split_clause,[],[f43,f258])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f218,plain,(
    spl4_27 ),
    inference(avatar_split_clause,[],[f48,f216])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f214,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f47,f212])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f200,plain,
    ( spl4_25
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f171,f162,f149,f65,f198])).

fof(f149,plain,
    ( spl4_19
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f171,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3
    | ~ spl4_4
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f166,f66])).

fof(f166,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(X3,k1_xboole_0)
    | ~ spl4_19
    | ~ spl4_20 ),
    inference(superposition,[],[f163,f150])).

fof(f150,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f149])).

fof(f179,plain,
    ( spl4_21
    | ~ spl4_4
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f172,f162,f116,f65,f176])).

fof(f116,plain,
    ( spl4_13
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f172,plain,
    ( sK1 = k2_xboole_0(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f167,f66])).

fof(f167,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0)
    | ~ spl4_13
    | ~ spl4_20 ),
    inference(superposition,[],[f163,f118])).

fof(f118,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f164,plain,(
    spl4_20 ),
    inference(avatar_split_clause,[],[f35,f162])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f151,plain,
    ( spl4_19
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f113,f109,f73,f149])).

fof(f73,plain,
    ( spl4_6
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f109,plain,
    ( spl4_12
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f113,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f110,f74])).

fof(f74,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f136,plain,
    ( spl4_16
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f114,f109,f78,f134])).

fof(f78,plain,
    ( spl4_7
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f114,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f110,f79])).

fof(f79,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f119,plain,
    ( spl4_13
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f112,f109,f50,f116])).

fof(f50,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f112,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_12 ),
    inference(resolution,[],[f110,f52])).

fof(f52,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f111,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f42,f109])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f95,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f33,f93])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f90,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f85,f82,f55,f87])).

fof(f55,plain,
    ( spl4_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f85,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl4_2
    | ~ spl4_8 ),
    inference(resolution,[],[f83,f57])).

fof(f57,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f84,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f80,plain,
    ( spl4_7
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f76,f73,f69,f78])).

fof(f69,plain,
    ( spl4_5
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f76,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f74,f70])).

fof(f70,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f75,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f63,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f28,f55])).

fof(f28,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f27,f50])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:13:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (14736)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (14736)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f689,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f53,f58,f63,f67,f71,f75,f80,f84,f90,f95,f111,f119,f136,f151,f164,f179,f200,f214,f218,f260,f265,f298,f313,f320,f333,f648,f683])).
% 0.21/0.43  fof(f683,plain,(
% 0.21/0.43    ~spl4_16 | ~spl4_21 | ~spl4_38 | spl4_41 | ~spl4_56),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f682])).
% 0.21/0.43  fof(f682,plain,(
% 0.21/0.43    $false | (~spl4_16 | ~spl4_21 | ~spl4_38 | spl4_41 | ~spl4_56)),
% 0.21/0.43    inference(subsumption_resolution,[],[f681,f135])).
% 0.21/0.43  fof(f135,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl4_16),
% 0.21/0.43    inference(avatar_component_clause,[],[f134])).
% 0.21/0.43  fof(f134,plain,(
% 0.21/0.43    spl4_16 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.43  fof(f681,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK2,sK2) | (~spl4_21 | ~spl4_38 | spl4_41 | ~spl4_56)),
% 0.21/0.43    inference(backward_demodulation,[],[f332,f680])).
% 0.21/0.43  fof(f680,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK2,sK0) | (~spl4_21 | ~spl4_38 | ~spl4_56)),
% 0.21/0.43    inference(forward_demodulation,[],[f665,f312])).
% 0.21/0.43  fof(f312,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK2,sK1) | ~spl4_38),
% 0.21/0.43    inference(avatar_component_clause,[],[f310])).
% 0.21/0.43  fof(f310,plain,(
% 0.21/0.43    spl4_38 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.21/0.43  fof(f665,plain,(
% 0.21/0.43    k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK0) | (~spl4_21 | ~spl4_56)),
% 0.21/0.43    inference(superposition,[],[f647,f178])).
% 0.21/0.43  fof(f178,plain,(
% 0.21/0.43    sK1 = k2_xboole_0(sK1,sK0) | ~spl4_21),
% 0.21/0.43    inference(avatar_component_clause,[],[f176])).
% 0.21/0.43  fof(f176,plain,(
% 0.21/0.43    spl4_21 <=> sK1 = k2_xboole_0(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.43  fof(f647,plain,(
% 0.21/0.43    ( ! [X16] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X16)) = k4_xboole_0(sK2,X16)) ) | ~spl4_56),
% 0.21/0.43    inference(avatar_component_clause,[],[f646])).
% 0.21/0.43  fof(f646,plain,(
% 0.21/0.43    spl4_56 <=> ! [X16] : k4_xboole_0(sK2,k2_xboole_0(sK1,X16)) = k4_xboole_0(sK2,X16)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.21/0.43  fof(f332,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | spl4_41),
% 0.21/0.43    inference(avatar_component_clause,[],[f330])).
% 0.21/0.43  fof(f330,plain,(
% 0.21/0.43    spl4_41 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.21/0.43  fof(f648,plain,(
% 0.21/0.43    spl4_56 | ~spl4_33 | ~spl4_38),
% 0.21/0.43    inference(avatar_split_clause,[],[f346,f310,f258,f646])).
% 0.21/0.43  fof(f258,plain,(
% 0.21/0.43    spl4_33 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.43  fof(f346,plain,(
% 0.21/0.43    ( ! [X16] : (k4_xboole_0(sK2,k2_xboole_0(sK1,X16)) = k4_xboole_0(sK2,X16)) ) | (~spl4_33 | ~spl4_38)),
% 0.21/0.43    inference(superposition,[],[f259,f312])).
% 0.21/0.43  fof(f259,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl4_33),
% 0.21/0.43    inference(avatar_component_clause,[],[f258])).
% 0.21/0.43  fof(f333,plain,(
% 0.21/0.43    ~spl4_41 | spl4_3 | ~spl4_39),
% 0.21/0.43    inference(avatar_split_clause,[],[f325,f318,f60,f330])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    spl4_3 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.43  fof(f318,plain,(
% 0.21/0.43    spl4_39 <=> ! [X3,X4] : (k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4)) | r1_xboole_0(X4,X3))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.21/0.43  fof(f325,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | (spl4_3 | ~spl4_39)),
% 0.21/0.43    inference(resolution,[],[f319,f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2) | spl4_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f60])).
% 0.21/0.43  fof(f319,plain,(
% 0.21/0.43    ( ! [X4,X3] : (r1_xboole_0(X4,X3) | k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4))) ) | ~spl4_39),
% 0.21/0.43    inference(avatar_component_clause,[],[f318])).
% 0.21/0.43  fof(f320,plain,(
% 0.21/0.43    spl4_39 | ~spl4_8 | ~spl4_26),
% 0.21/0.43    inference(avatar_split_clause,[],[f231,f212,f82,f318])).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl4_8 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.43  fof(f212,plain,(
% 0.21/0.43    spl4_26 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.43  fof(f231,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X4)) | r1_xboole_0(X4,X3)) ) | (~spl4_8 | ~spl4_26)),
% 0.21/0.43    inference(resolution,[],[f213,f83])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f82])).
% 0.21/0.43  fof(f213,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_26),
% 0.21/0.43    inference(avatar_component_clause,[],[f212])).
% 0.21/0.43  fof(f313,plain,(
% 0.21/0.43    spl4_38 | ~spl4_10 | ~spl4_25 | ~spl4_37),
% 0.21/0.43    inference(avatar_split_clause,[],[f303,f295,f198,f93,f310])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl4_10 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.43  fof(f198,plain,(
% 0.21/0.43    spl4_25 <=> ! [X3,X4] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.21/0.43  fof(f295,plain,(
% 0.21/0.43    spl4_37 <=> k4_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.43  fof(f303,plain,(
% 0.21/0.43    sK2 = k4_xboole_0(sK2,sK1) | (~spl4_10 | ~spl4_25 | ~spl4_37)),
% 0.21/0.43    inference(forward_demodulation,[],[f299,f199])).
% 0.21/0.43  fof(f199,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) ) | ~spl4_25),
% 0.21/0.43    inference(avatar_component_clause,[],[f198])).
% 0.21/0.43  fof(f299,plain,(
% 0.21/0.43    k4_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | (~spl4_10 | ~spl4_37)),
% 0.21/0.43    inference(superposition,[],[f297,f94])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl4_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f93])).
% 0.21/0.43  fof(f297,plain,(
% 0.21/0.43    k4_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) | ~spl4_37),
% 0.21/0.43    inference(avatar_component_clause,[],[f295])).
% 0.21/0.43  fof(f298,plain,(
% 0.21/0.43    spl4_37 | ~spl4_4 | ~spl4_20 | ~spl4_34),
% 0.21/0.43    inference(avatar_split_clause,[],[f270,f262,f162,f65,f295])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl4_4 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.43  fof(f162,plain,(
% 0.21/0.43    spl4_20 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.21/0.43  fof(f262,plain,(
% 0.21/0.43    spl4_34 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.43  fof(f270,plain,(
% 0.21/0.43    k4_xboole_0(sK2,sK1) = k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) | (~spl4_4 | ~spl4_20 | ~spl4_34)),
% 0.21/0.43    inference(forward_demodulation,[],[f267,f66])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f65])).
% 0.21/0.43  fof(f267,plain,(
% 0.21/0.43    k2_xboole_0(k4_xboole_0(sK2,sK1),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK1),k1_xboole_0) | (~spl4_20 | ~spl4_34)),
% 0.21/0.43    inference(superposition,[],[f163,f264])).
% 0.21/0.43  fof(f264,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | ~spl4_34),
% 0.21/0.43    inference(avatar_component_clause,[],[f262])).
% 0.21/0.43  fof(f163,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl4_20),
% 0.21/0.43    inference(avatar_component_clause,[],[f162])).
% 0.21/0.43  fof(f265,plain,(
% 0.21/0.43    spl4_34 | ~spl4_9 | ~spl4_27),
% 0.21/0.43    inference(avatar_split_clause,[],[f239,f216,f87,f262])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl4_9 <=> r1_xboole_0(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.43  fof(f216,plain,(
% 0.21/0.43    spl4_27 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.43  fof(f239,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)) | (~spl4_9 | ~spl4_27)),
% 0.21/0.43    inference(resolution,[],[f217,f89])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK1) | ~spl4_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f217,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl4_27),
% 0.21/0.43    inference(avatar_component_clause,[],[f216])).
% 0.21/0.43  fof(f260,plain,(
% 0.21/0.43    spl4_33),
% 0.21/0.43    inference(avatar_split_clause,[],[f43,f258])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.43  fof(f218,plain,(
% 0.21/0.43    spl4_27),
% 0.21/0.43    inference(avatar_split_clause,[],[f48,f216])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(definition_unfolding,[],[f40,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(nnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.43  fof(f214,plain,(
% 0.21/0.43    spl4_26),
% 0.21/0.43    inference(avatar_split_clause,[],[f47,f212])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f41,f34])).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f26])).
% 0.21/0.43  fof(f200,plain,(
% 0.21/0.43    spl4_25 | ~spl4_4 | ~spl4_19 | ~spl4_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f171,f162,f149,f65,f198])).
% 0.21/0.43  fof(f149,plain,(
% 0.21/0.43    spl4_19 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.43  fof(f171,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) ) | (~spl4_4 | ~spl4_19 | ~spl4_20)),
% 0.21/0.43    inference(forward_demodulation,[],[f166,f66])).
% 0.21/0.43  fof(f166,plain,(
% 0.21/0.43    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = k2_xboole_0(X3,k1_xboole_0)) ) | (~spl4_19 | ~spl4_20)),
% 0.21/0.43    inference(superposition,[],[f163,f150])).
% 0.21/0.43  fof(f150,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl4_19),
% 0.21/0.43    inference(avatar_component_clause,[],[f149])).
% 0.21/0.43  fof(f179,plain,(
% 0.21/0.43    spl4_21 | ~spl4_4 | ~spl4_13 | ~spl4_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f172,f162,f116,f65,f176])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    spl4_13 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.43  fof(f172,plain,(
% 0.21/0.43    sK1 = k2_xboole_0(sK1,sK0) | (~spl4_4 | ~spl4_13 | ~spl4_20)),
% 0.21/0.43    inference(forward_demodulation,[],[f167,f66])).
% 0.21/0.43  fof(f167,plain,(
% 0.21/0.43    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) | (~spl4_13 | ~spl4_20)),
% 0.21/0.43    inference(superposition,[],[f163,f118])).
% 0.21/0.43  fof(f118,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f116])).
% 0.21/0.43  fof(f164,plain,(
% 0.21/0.43    spl4_20),
% 0.21/0.43    inference(avatar_split_clause,[],[f35,f162])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.43  fof(f151,plain,(
% 0.21/0.43    spl4_19 | ~spl4_6 | ~spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f113,f109,f73,f149])).
% 0.21/0.43  fof(f73,plain,(
% 0.21/0.43    spl4_6 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    spl4_12 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl4_6 | ~spl4_12)),
% 0.21/0.43    inference(resolution,[],[f110,f74])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl4_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f73])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl4_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f109])).
% 0.21/0.43  fof(f136,plain,(
% 0.21/0.43    spl4_16 | ~spl4_7 | ~spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f114,f109,f78,f134])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    spl4_7 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl4_7 | ~spl4_12)),
% 0.21/0.43    inference(resolution,[],[f110,f79])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl4_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f78])).
% 0.21/0.43  fof(f119,plain,(
% 0.21/0.43    spl4_13 | ~spl4_1 | ~spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f112,f109,f50,f116])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    spl4_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_12)),
% 0.21/0.43    inference(resolution,[],[f110,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl4_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f50])).
% 0.21/0.43  fof(f111,plain,(
% 0.21/0.43    spl4_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f42,f109])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.21/0.43    inference(unused_predicate_definition_removal,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.43  fof(f95,plain,(
% 0.21/0.43    spl4_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f33,f93])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.43  fof(f90,plain,(
% 0.21/0.43    spl4_9 | ~spl4_2 | ~spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f82,f55,f87])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl4_2 <=> r1_xboole_0(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    r1_xboole_0(sK2,sK1) | (~spl4_2 | ~spl4_8)),
% 0.21/0.43    inference(resolution,[],[f83,f57])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2) | ~spl4_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl4_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f39,f82])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.43  fof(f80,plain,(
% 0.21/0.43    spl4_7 | ~spl4_5 | ~spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f76,f73,f69,f78])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl4_5 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl4_5 | ~spl4_6)),
% 0.21/0.43    inference(superposition,[],[f74,f70])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl4_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f69])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    spl4_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f32,f73])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl4_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f31,f69])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    spl4_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f30,f65])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    ~spl4_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f29,f60])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    inference(negated_conjecture,[],[f13])).
% 0.21/0.43  fof(f13,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    spl4_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f55])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    r1_xboole_0(sK1,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl4_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f50])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (14736)------------------------------
% 0.21/0.43  % (14736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (14736)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (14736)Memory used [KB]: 6524
% 0.21/0.43  % (14736)Time elapsed: 0.018 s
% 0.21/0.43  % (14736)------------------------------
% 0.21/0.43  % (14736)------------------------------
% 0.21/0.43  % (14728)Success in time 0.081 s
%------------------------------------------------------------------------------
