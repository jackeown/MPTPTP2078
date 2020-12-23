%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 181 expanded)
%              Number of leaves         :   30 (  86 expanded)
%              Depth                    :    7
%              Number of atoms          :  241 ( 393 expanded)
%              Number of equality atoms :   71 ( 134 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f561,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f47,f55,f59,f64,f96,f112,f136,f140,f146,f155,f177,f275,f317,f375,f383,f452,f482,f512,f557])).

fof(f557,plain,
    ( ~ spl3_5
    | spl3_19
    | ~ spl3_33
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | ~ spl3_5
    | spl3_19
    | ~ spl3_33
    | ~ spl3_43
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f555,f481])).

fof(f481,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl3_45
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f555,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl3_5
    | spl3_19
    | ~ spl3_33
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f145,f554])).

fof(f554,plain,
    ( ! [X0] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl3_5
    | ~ spl3_33
    | ~ spl3_43
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f549,f391])).

fof(f391,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl3_5
    | ~ spl3_43 ),
    inference(superposition,[],[f382,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f382,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f381])).

fof(f381,plain,
    ( spl3_43
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f549,plain,
    ( ! [X0] : k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl3_33
    | ~ spl3_47 ),
    inference(superposition,[],[f274,f511])).

fof(f511,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl3_47
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f274,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl3_33
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f145,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_19
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f512,plain,
    ( spl3_47
    | ~ spl3_42
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f456,f450,f372,f509])).

fof(f372,plain,
    ( spl3_42
  <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f450,plain,
    ( spl3_44
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f456,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_42
    | ~ spl3_44 ),
    inference(superposition,[],[f451,f374])).

fof(f374,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f372])).

fof(f451,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f450])).

fof(f482,plain,
    ( spl3_45
    | ~ spl3_20
    | ~ spl3_42
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f468,f450,f372,f152,f479])).

fof(f152,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f468,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl3_20
    | ~ spl3_42
    | ~ spl3_44 ),
    inference(backward_demodulation,[],[f154,f456])).

fof(f154,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f452,plain,
    ( spl3_44
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f395,f381,f110,f53,f450])).

fof(f110,plain,
    ( spl3_14
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f395,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_5
    | ~ spl3_14
    | ~ spl3_43 ),
    inference(backward_demodulation,[],[f111,f391])).

fof(f111,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f383,plain,
    ( spl3_43
    | ~ spl3_12
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f369,f315,f94,f381])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f315,plain,
    ( spl3_39
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f369,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2
    | ~ spl3_12
    | ~ spl3_39 ),
    inference(superposition,[],[f316,f95])).

fof(f95,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f316,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f315])).

fof(f375,plain,
    ( spl3_42
    | ~ spl3_20
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f368,f315,f152,f372])).

fof(f368,plain,
    ( sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl3_20
    | ~ spl3_39 ),
    inference(superposition,[],[f316,f154])).

fof(f317,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f229,f175,f53,f315])).

fof(f175,plain,
    ( spl3_23
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f229,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl3_5
    | ~ spl3_23 ),
    inference(superposition,[],[f176,f54])).

fof(f176,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f175])).

fof(f275,plain,(
    spl3_33 ),
    inference(avatar_split_clause,[],[f33,f273])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f29,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f177,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f30,f175])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f155,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f150,f138,f35,f152])).

fof(f35,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f138,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f150,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(resolution,[],[f139,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f146,plain,
    ( ~ spl3_19
    | spl3_2
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f141,f134,f40,f143])).

fof(f40,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f134,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f141,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | spl3_2
    | ~ spl3_17 ),
    inference(resolution,[],[f135,f42])).

fof(f42,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f135,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f140,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f32,f138])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f136,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f31,f134])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f108,f94,f62,f110])).

fof(f62,plain,
    ( spl3_7
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f108,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0)
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(superposition,[],[f95,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f24,f94])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f64,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f57,f45,f62])).

fof(f45,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

% (31538)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f43,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (31530)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (31525)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (31534)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (31541)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (31535)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (31542)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (31527)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (31532)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (31537)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (31528)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31531)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (31529)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (31539)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (31532)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (31533)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (31540)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f38,f43,f47,f55,f59,f64,f96,f112,f136,f140,f146,f155,f177,f275,f317,f375,f383,f452,f482,f512,f557])).
% 0.21/0.49  fof(f557,plain,(
% 0.21/0.49    ~spl3_5 | spl3_19 | ~spl3_33 | ~spl3_43 | ~spl3_45 | ~spl3_47),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f556])).
% 0.21/0.49  fof(f556,plain,(
% 0.21/0.49    $false | (~spl3_5 | spl3_19 | ~spl3_33 | ~spl3_43 | ~spl3_45 | ~spl3_47)),
% 0.21/0.49    inference(subsumption_resolution,[],[f555,f481])).
% 0.21/0.49  fof(f481,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | ~spl3_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f479])).
% 0.21/0.49  fof(f479,plain,(
% 0.21/0.49    spl3_45 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.49  fof(f555,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,sK0) | (~spl3_5 | spl3_19 | ~spl3_33 | ~spl3_43 | ~spl3_47)),
% 0.21/0.49    inference(backward_demodulation,[],[f145,f554])).
% 0.21/0.49  fof(f554,plain,(
% 0.21/0.49    ( ! [X0] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ) | (~spl3_5 | ~spl3_33 | ~spl3_43 | ~spl3_47)),
% 0.21/0.49    inference(forward_demodulation,[],[f549,f391])).
% 0.21/0.49  fof(f391,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | (~spl3_5 | ~spl3_43)),
% 0.21/0.49    inference(superposition,[],[f382,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.49  fof(f382,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) ) | ~spl3_43),
% 0.21/0.49    inference(avatar_component_clause,[],[f381])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    spl3_43 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.49  fof(f549,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) = k4_xboole_0(sK0,k4_xboole_0(sK1,X0))) ) | (~spl3_33 | ~spl3_47)),
% 0.21/0.49    inference(superposition,[],[f274,f511])).
% 0.21/0.49  fof(f511,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_47),
% 0.21/0.49    inference(avatar_component_clause,[],[f509])).
% 0.21/0.49  fof(f509,plain,(
% 0.21/0.49    spl3_47 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f273])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    spl3_33 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | spl3_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl3_19 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.49  fof(f512,plain,(
% 0.21/0.49    spl3_47 | ~spl3_42 | ~spl3_44),
% 0.21/0.49    inference(avatar_split_clause,[],[f456,f450,f372,f509])).
% 0.21/0.49  fof(f372,plain,(
% 0.21/0.49    spl3_42 <=> sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.49  fof(f450,plain,(
% 0.21/0.49    spl3_44 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.49  fof(f456,plain,(
% 0.21/0.49    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_42 | ~spl3_44)),
% 0.21/0.49    inference(superposition,[],[f451,f374])).
% 0.21/0.49  fof(f374,plain,(
% 0.21/0.49    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl3_42),
% 0.21/0.49    inference(avatar_component_clause,[],[f372])).
% 0.21/0.49  fof(f451,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f450])).
% 0.21/0.49  fof(f482,plain,(
% 0.21/0.49    spl3_45 | ~spl3_20 | ~spl3_42 | ~spl3_44),
% 0.21/0.49    inference(avatar_split_clause,[],[f468,f450,f372,f152,f479])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    spl3_20 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.49  fof(f468,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl3_20 | ~spl3_42 | ~spl3_44)),
% 0.21/0.49    inference(backward_demodulation,[],[f154,f456])).
% 0.21/0.49  fof(f154,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f152])).
% 0.21/0.49  fof(f452,plain,(
% 0.21/0.49    spl3_44 | ~spl3_5 | ~spl3_14 | ~spl3_43),
% 0.21/0.49    inference(avatar_split_clause,[],[f395,f381,f110,f53,f450])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl3_14 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.49  fof(f395,plain,(
% 0.21/0.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl3_5 | ~spl3_14 | ~spl3_43)),
% 0.21/0.49    inference(backward_demodulation,[],[f111,f391])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0)) ) | ~spl3_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f110])).
% 0.21/0.49  fof(f383,plain,(
% 0.21/0.49    spl3_43 | ~spl3_12 | ~spl3_39),
% 0.21/0.49    inference(avatar_split_clause,[],[f369,f315,f94,f381])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    spl3_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    spl3_39 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.49  fof(f369,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) ) | (~spl3_12 | ~spl3_39)),
% 0.21/0.49    inference(superposition,[],[f316,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f94])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | ~spl3_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f315])).
% 0.21/0.49  fof(f375,plain,(
% 0.21/0.49    spl3_42 | ~spl3_20 | ~spl3_39),
% 0.21/0.49    inference(avatar_split_clause,[],[f368,f315,f152,f372])).
% 0.21/0.49  fof(f368,plain,(
% 0.21/0.49    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl3_20 | ~spl3_39)),
% 0.21/0.49    inference(superposition,[],[f316,f154])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    spl3_39 | ~spl3_5 | ~spl3_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f229,f175,f53,f315])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl3_23 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | (~spl3_5 | ~spl3_23)),
% 0.21/0.49    inference(superposition,[],[f176,f54])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f175])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    spl3_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f273])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f29,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl3_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f175])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl3_20 | ~spl3_1 | ~spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f150,f138,f35,f152])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    spl3_18 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_18)),
% 0.21/0.49    inference(resolution,[],[f139,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f35])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f138])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    ~spl3_19 | spl3_2 | ~spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f134,f40,f143])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl3_17 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | (spl3_2 | ~spl3_17)),
% 0.21/0.49    inference(resolution,[],[f135,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f40])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f134])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl3_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f138])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f26,f23])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.49    inference(nnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl3_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f134])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f27,f23])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    spl3_14 | ~spl3_7 | ~spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f108,f94,f62,f110])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl3_7 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0)) ) | (~spl3_7 | ~spl3_12)),
% 0.21/0.49    inference(superposition,[],[f95,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    spl3_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f94])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl3_7 | ~spl3_3 | ~spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f60,f57,f45,f62])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    spl3_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    spl3_6 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.21/0.49    inference(resolution,[],[f58,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f45])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f57])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    spl3_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f57])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.21/0.49    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl3_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  % (31538)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl3_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f40])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    spl3_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f35])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    r1_xboole_0(sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (31532)------------------------------
% 0.21/0.49  % (31532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31532)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (31532)Memory used [KB]: 6396
% 0.21/0.49  % (31532)Time elapsed: 0.016 s
% 0.21/0.49  % (31532)------------------------------
% 0.21/0.49  % (31532)------------------------------
% 0.21/0.49  % (31522)Success in time 0.138 s
%------------------------------------------------------------------------------
