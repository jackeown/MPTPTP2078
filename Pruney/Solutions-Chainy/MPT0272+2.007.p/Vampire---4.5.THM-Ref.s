%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:12 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 152 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :    6
%              Number of atoms          :  239 ( 354 expanded)
%              Number of equality atoms :   75 ( 125 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2295,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f59,f67,f71,f75,f83,f87,f96,f117,f125,f162,f199,f217,f269,f355,f476,f1238,f2271,f2289])).

fof(f2289,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_33
    | ~ spl2_61
    | ~ spl2_98 ),
    inference(avatar_contradiction_clause,[],[f2288])).

fof(f2288,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_33
    | ~ spl2_61
    | ~ spl2_98 ),
    inference(subsumption_resolution,[],[f1247,f2287])).

fof(f2287,plain,
    ( ~ r1_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | spl2_1
    | ~ spl2_5
    | ~ spl2_98 ),
    inference(forward_demodulation,[],[f2272,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl2_5
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f2272,plain,
    ( ~ r1_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))
    | spl2_1
    | ~ spl2_98 ),
    inference(unit_resulting_resolution,[],[f49,f2270])).

fof(f2270,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(k5_xboole_0(X2,X3),X2)
        | k1_xboole_0 = k4_xboole_0(X2,X3) )
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f2269])).

fof(f2269,plain,
    ( spl2_98
  <=> ! [X3,X2] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_xboole_0(k5_xboole_0(X2,X3),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f49,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_1
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1247,plain,
    ( r1_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl2_33
    | ~ spl2_61 ),
    inference(unit_resulting_resolution,[],[f354,f1237])).

fof(f1237,plain,
    ( ! [X10,X9] :
        ( ~ r1_xboole_0(X10,X9)
        | r1_xboole_0(X9,X10) )
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f1236])).

fof(f1236,plain,
    ( spl2_61
  <=> ! [X9,X10] :
        ( r1_xboole_0(X9,X10)
        | ~ r1_xboole_0(X10,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f354,plain,
    ( r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl2_33
  <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f2271,plain,
    ( spl2_98
    | ~ spl2_29
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f482,f474,f267,f2269])).

fof(f267,plain,
    ( spl2_29
  <=> ! [X3,X4] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f474,plain,
    ( spl2_41
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f482,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,X3)
        | ~ r1_xboole_0(k5_xboole_0(X2,X3),X2) )
    | ~ spl2_29
    | ~ spl2_41 ),
    inference(superposition,[],[f475,f268])).

fof(f268,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f267])).

fof(f475,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f474])).

fof(f1238,plain,
    ( spl2_61
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f290,f267,f85,f1236])).

fof(f85,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f290,plain,
    ( ! [X10,X9] :
        ( r1_xboole_0(X9,X10)
        | ~ r1_xboole_0(X10,X9) )
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(trivial_inequality_removal,[],[f283])).

fof(f283,plain,
    ( ! [X10,X9] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(X9,X10)
        | ~ r1_xboole_0(X10,X9) )
    | ~ spl2_10
    | ~ spl2_29 ),
    inference(superposition,[],[f86,f268])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) != k1_xboole_0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f476,plain,
    ( spl2_41
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f185,f160,f94,f69,f57,f474])).

fof(f57,plain,
    ( spl2_3
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f69,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f94,plain,
    ( spl2_11
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f160,plain,
    ( spl2_19
  <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f185,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f184,f132])).

fof(f132,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f95,f70])).

fof(f70,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f95,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f184,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_19 ),
    inference(forward_demodulation,[],[f167,f70])).

fof(f167,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(superposition,[],[f161,f58])).

fof(f58,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f161,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f160])).

fof(f355,plain,
    ( spl2_33
    | ~ spl2_7
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f255,f214,f73,f352])).

fof(f73,plain,
    ( spl2_7
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f214,plain,
    ( spl2_24
  <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f255,plain,
    ( r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))
    | ~ spl2_7
    | ~ spl2_24 ),
    inference(superposition,[],[f74,f216])).

fof(f216,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f214])).

fof(f74,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f269,plain,
    ( spl2_29
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f103,f81,f69,f267])).

fof(f81,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f103,plain,
    ( ! [X4,X3] :
        ( k1_xboole_0 = k3_xboole_0(X4,X3)
        | ~ r1_xboole_0(X3,X4) )
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(superposition,[],[f82,f70])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f217,plain,
    ( spl2_24
    | ~ spl2_13
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f209,f196,f115,f214])).

fof(f115,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f196,plain,
    ( spl2_21
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f209,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl2_13
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f198,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f115])).

fof(f198,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f199,plain,
    ( spl2_21
    | spl2_2
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f150,f123,f52,f196])).

fof(f52,plain,
    ( spl2_2
  <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f123,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f150,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_2
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f54,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f123])).

fof(f54,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f162,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f41,f160])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f125,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f39,f123])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f117,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f35,f115])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f96,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f34,f94])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f87,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f83,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f71,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f31,f69])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f67,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f59,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f55,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f52])).

fof(f27,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f50,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:31:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (6479)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (6474)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (6482)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (6480)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (6478)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (6484)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (6475)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (6489)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (6487)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (6488)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (6486)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (6491)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (6477)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.51  % (6476)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (6481)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (6483)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (6490)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.33/0.54  % (6485)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 1.33/0.54  % (6485)Refutation not found, incomplete strategy% (6485)------------------------------
% 1.33/0.54  % (6485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (6485)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (6485)Memory used [KB]: 10618
% 1.33/0.54  % (6485)Time elapsed: 0.126 s
% 1.33/0.54  % (6485)------------------------------
% 1.33/0.54  % (6485)------------------------------
% 1.51/0.56  % (6479)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f2295,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f50,f55,f59,f67,f71,f75,f83,f87,f96,f117,f125,f162,f199,f217,f269,f355,f476,f1238,f2271,f2289])).
% 1.51/0.56  fof(f2289,plain,(
% 1.51/0.56    spl2_1 | ~spl2_5 | ~spl2_33 | ~spl2_61 | ~spl2_98),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f2288])).
% 1.51/0.56  fof(f2288,plain,(
% 1.51/0.56    $false | (spl2_1 | ~spl2_5 | ~spl2_33 | ~spl2_61 | ~spl2_98)),
% 1.51/0.56    inference(subsumption_resolution,[],[f1247,f2287])).
% 1.51/0.56  fof(f2287,plain,(
% 1.51/0.56    ~r1_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (spl2_1 | ~spl2_5 | ~spl2_98)),
% 1.51/0.56    inference(forward_demodulation,[],[f2272,f66])).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) ) | ~spl2_5),
% 1.51/0.56    inference(avatar_component_clause,[],[f65])).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    spl2_5 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.51/0.56  fof(f2272,plain,(
% 1.51/0.56    ~r1_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) | (spl2_1 | ~spl2_98)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f49,f2270])).
% 1.51/0.56  fof(f2270,plain,(
% 1.51/0.56    ( ! [X2,X3] : (~r1_xboole_0(k5_xboole_0(X2,X3),X2) | k1_xboole_0 = k4_xboole_0(X2,X3)) ) | ~spl2_98),
% 1.51/0.56    inference(avatar_component_clause,[],[f2269])).
% 1.51/0.56  fof(f2269,plain,(
% 1.51/0.56    spl2_98 <=> ! [X3,X2] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_xboole_0(k5_xboole_0(X2,X3),X2))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_1),
% 1.51/0.56    inference(avatar_component_clause,[],[f47])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    spl2_1 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.51/0.56  fof(f1247,plain,(
% 1.51/0.56    r1_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) | (~spl2_33 | ~spl2_61)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f354,f1237])).
% 1.51/0.56  fof(f1237,plain,(
% 1.51/0.56    ( ! [X10,X9] : (~r1_xboole_0(X10,X9) | r1_xboole_0(X9,X10)) ) | ~spl2_61),
% 1.51/0.56    inference(avatar_component_clause,[],[f1236])).
% 1.51/0.56  fof(f1236,plain,(
% 1.51/0.56    spl2_61 <=> ! [X9,X10] : (r1_xboole_0(X9,X10) | ~r1_xboole_0(X10,X9))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 1.51/0.56  fof(f354,plain,(
% 1.51/0.56    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | ~spl2_33),
% 1.51/0.56    inference(avatar_component_clause,[],[f352])).
% 1.51/0.56  fof(f352,plain,(
% 1.51/0.56    spl2_33 <=> r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 1.51/0.56  fof(f2271,plain,(
% 1.51/0.56    spl2_98 | ~spl2_29 | ~spl2_41),
% 1.51/0.56    inference(avatar_split_clause,[],[f482,f474,f267,f2269])).
% 1.51/0.56  fof(f267,plain,(
% 1.51/0.56    spl2_29 <=> ! [X3,X4] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 1.51/0.56  fof(f474,plain,(
% 1.51/0.56    spl2_41 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 1.51/0.56  fof(f482,plain,(
% 1.51/0.56    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,X3) | ~r1_xboole_0(k5_xboole_0(X2,X3),X2)) ) | (~spl2_29 | ~spl2_41)),
% 1.51/0.56    inference(superposition,[],[f475,f268])).
% 1.51/0.56  fof(f268,plain,(
% 1.51/0.56    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) ) | ~spl2_29),
% 1.51/0.56    inference(avatar_component_clause,[],[f267])).
% 1.51/0.56  fof(f475,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) ) | ~spl2_41),
% 1.51/0.56    inference(avatar_component_clause,[],[f474])).
% 1.51/0.56  fof(f1238,plain,(
% 1.51/0.56    spl2_61 | ~spl2_10 | ~spl2_29),
% 1.51/0.56    inference(avatar_split_clause,[],[f290,f267,f85,f1236])).
% 1.51/0.56  fof(f85,plain,(
% 1.51/0.56    spl2_10 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 1.51/0.56  fof(f290,plain,(
% 1.51/0.56    ( ! [X10,X9] : (r1_xboole_0(X9,X10) | ~r1_xboole_0(X10,X9)) ) | (~spl2_10 | ~spl2_29)),
% 1.51/0.56    inference(trivial_inequality_removal,[],[f283])).
% 1.51/0.56  fof(f283,plain,(
% 1.51/0.56    ( ! [X10,X9] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X9,X10) | ~r1_xboole_0(X10,X9)) ) | (~spl2_10 | ~spl2_29)),
% 1.51/0.56    inference(superposition,[],[f86,f268])).
% 1.51/0.56  fof(f86,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) ) | ~spl2_10),
% 1.51/0.56    inference(avatar_component_clause,[],[f85])).
% 1.51/0.56  fof(f476,plain,(
% 1.51/0.56    spl2_41 | ~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_19),
% 1.51/0.56    inference(avatar_split_clause,[],[f185,f160,f94,f69,f57,f474])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    spl2_3 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.51/0.56  fof(f94,plain,(
% 1.51/0.56    spl2_11 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.51/0.56  fof(f160,plain,(
% 1.51/0.56    spl2_19 <=> ! [X1,X0,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 1.51/0.56  fof(f185,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_6 | ~spl2_11 | ~spl2_19)),
% 1.51/0.56    inference(forward_demodulation,[],[f184,f132])).
% 1.51/0.56  fof(f132,plain,(
% 1.51/0.56    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) ) | (~spl2_6 | ~spl2_11)),
% 1.51/0.56    inference(superposition,[],[f95,f70])).
% 1.51/0.56  fof(f70,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 1.51/0.56    inference(avatar_component_clause,[],[f69])).
% 1.51/0.56  fof(f95,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_11),
% 1.51/0.56    inference(avatar_component_clause,[],[f94])).
% 1.51/0.56  fof(f184,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_6 | ~spl2_19)),
% 1.51/0.56    inference(forward_demodulation,[],[f167,f70])).
% 1.51/0.56  fof(f167,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) ) | (~spl2_3 | ~spl2_19)),
% 1.51/0.56    inference(superposition,[],[f161,f58])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_3),
% 1.51/0.56    inference(avatar_component_clause,[],[f57])).
% 1.51/0.56  fof(f161,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) ) | ~spl2_19),
% 1.51/0.56    inference(avatar_component_clause,[],[f160])).
% 1.51/0.56  fof(f355,plain,(
% 1.51/0.56    spl2_33 | ~spl2_7 | ~spl2_24),
% 1.51/0.56    inference(avatar_split_clause,[],[f255,f214,f73,f352])).
% 1.51/0.56  fof(f73,plain,(
% 1.51/0.56    spl2_7 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.51/0.56  fof(f214,plain,(
% 1.51/0.56    spl2_24 <=> k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 1.51/0.56  fof(f255,plain,(
% 1.51/0.56    r1_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) | (~spl2_7 | ~spl2_24)),
% 1.51/0.56    inference(superposition,[],[f74,f216])).
% 1.51/0.56  fof(f216,plain,(
% 1.51/0.56    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl2_24),
% 1.51/0.56    inference(avatar_component_clause,[],[f214])).
% 1.51/0.56  fof(f74,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ) | ~spl2_7),
% 1.51/0.56    inference(avatar_component_clause,[],[f73])).
% 1.51/0.56  fof(f269,plain,(
% 1.51/0.56    spl2_29 | ~spl2_6 | ~spl2_9),
% 1.51/0.56    inference(avatar_split_clause,[],[f103,f81,f69,f267])).
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    spl2_9 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.51/0.56  fof(f103,plain,(
% 1.51/0.56    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(X4,X3) | ~r1_xboole_0(X3,X4)) ) | (~spl2_6 | ~spl2_9)),
% 1.51/0.56    inference(superposition,[],[f82,f70])).
% 1.51/0.56  fof(f82,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_9),
% 1.51/0.56    inference(avatar_component_clause,[],[f81])).
% 1.51/0.56  fof(f217,plain,(
% 1.51/0.56    spl2_24 | ~spl2_13 | ~spl2_21),
% 1.51/0.56    inference(avatar_split_clause,[],[f209,f196,f115,f214])).
% 1.51/0.56  fof(f115,plain,(
% 1.51/0.56    spl2_13 <=> ! [X1,X0] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.51/0.56  fof(f196,plain,(
% 1.51/0.56    spl2_21 <=> r2_hidden(sK0,sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.51/0.56  fof(f209,plain,(
% 1.51/0.56    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) | (~spl2_13 | ~spl2_21)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f198,f116])).
% 1.51/0.56  fof(f116,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) ) | ~spl2_13),
% 1.51/0.56    inference(avatar_component_clause,[],[f115])).
% 1.51/0.56  fof(f198,plain,(
% 1.51/0.56    r2_hidden(sK0,sK1) | ~spl2_21),
% 1.51/0.56    inference(avatar_component_clause,[],[f196])).
% 1.51/0.56  fof(f199,plain,(
% 1.51/0.56    spl2_21 | spl2_2 | ~spl2_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f150,f123,f52,f196])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    spl2_2 <=> k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.51/0.56  fof(f123,plain,(
% 1.51/0.56    spl2_15 <=> ! [X1,X0] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.51/0.56  fof(f150,plain,(
% 1.51/0.56    r2_hidden(sK0,sK1) | (spl2_2 | ~spl2_15)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f54,f124])).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) ) | ~spl2_15),
% 1.51/0.56    inference(avatar_component_clause,[],[f123])).
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | spl2_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f52])).
% 1.51/0.56  fof(f162,plain,(
% 1.51/0.56    spl2_19),
% 1.51/0.56    inference(avatar_split_clause,[],[f41,f160])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.51/0.56  fof(f125,plain,(
% 1.51/0.56    spl2_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f39,f123])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.51/0.56    inference(nnf_transformation,[],[f16])).
% 1.51/0.56  fof(f16,axiom,(
% 1.51/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.51/0.56  fof(f117,plain,(
% 1.51/0.56    spl2_13),
% 1.51/0.56    inference(avatar_split_clause,[],[f35,f115])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f21])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f15])).
% 1.51/0.56  fof(f15,axiom,(
% 1.51/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.51/0.56  fof(f96,plain,(
% 1.51/0.56    spl2_11),
% 1.51/0.56    inference(avatar_split_clause,[],[f34,f94])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f6])).
% 1.51/0.56  fof(f6,axiom,(
% 1.51/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.51/0.56  fof(f87,plain,(
% 1.51/0.56    spl2_10),
% 1.51/0.56    inference(avatar_split_clause,[],[f37,f85])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.51/0.56    inference(nnf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.51/0.56  fof(f83,plain,(
% 1.51/0.56    spl2_9),
% 1.51/0.56    inference(avatar_split_clause,[],[f36,f81])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f24])).
% 1.51/0.56  fof(f75,plain,(
% 1.51/0.56    spl2_7),
% 1.51/0.56    inference(avatar_split_clause,[],[f32,f73])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.51/0.56  fof(f71,plain,(
% 1.51/0.56    spl2_6),
% 1.51/0.56    inference(avatar_split_clause,[],[f31,f69])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    spl2_5),
% 1.51/0.56    inference(avatar_split_clause,[],[f30,f65])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    spl2_3),
% 1.51/0.56    inference(avatar_split_clause,[],[f29,f57])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.51/0.56    inference(rectify,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ~spl2_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f27,f52])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.56    inference(ennf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.56    inference(negated_conjecture,[],[f17])).
% 1.51/0.56  fof(f17,conjecture,(
% 1.51/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.51/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ~spl2_1),
% 1.51/0.56    inference(avatar_split_clause,[],[f26,f47])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f23])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (6479)------------------------------
% 1.51/0.56  % (6479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (6479)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (6479)Memory used [KB]: 8059
% 1.51/0.56  % (6479)Time elapsed: 0.132 s
% 1.51/0.56  % (6479)------------------------------
% 1.51/0.56  % (6479)------------------------------
% 1.51/0.56  % (6473)Success in time 0.199 s
%------------------------------------------------------------------------------
