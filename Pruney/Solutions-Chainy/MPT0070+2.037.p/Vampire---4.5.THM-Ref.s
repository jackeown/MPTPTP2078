%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 155 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :    8
%              Number of atoms          :  205 ( 341 expanded)
%              Number of equality atoms :   60 ( 106 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f66,f70,f74,f80,f87,f91,f108,f114,f150,f162])).

fof(f162,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_10
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_10
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f160,f79])).

fof(f79,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f160,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f159,f55])).

fof(f55,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_5
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f159,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f158,f51])).

fof(f51,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f158,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f151,f55])).

fof(f151,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)))
    | ~ spl3_13
    | ~ spl3_15 ),
    inference(superposition,[],[f149,f107])).

fof(f107,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_13
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f149,plain,
    ( ! [X11] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X11))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl3_15
  <=> ! [X11] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f150,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f135,f112,f63,f50,f148])).

fof(f63,plain,
    ( spl3_7
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f112,plain,
    ( spl3_14
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f135,plain,
    ( ! [X11] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X11))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f119,f51])).

fof(f119,plain,
    ( ! [X11] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X11))
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f113,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f113,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f112])).

fof(f114,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f32,f112])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f27,f23,f23,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f108,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f102,f89,f84,f50,f105])).

fof(f84,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f89,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f102,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f97,f51])).

fof(f97,plain,
    ( k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0)
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(superposition,[],[f90,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f84])).

fof(f90,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f29,f89])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f87,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f81,f72,f40,f84])).

fof(f40,plain,
    ( spl3_2
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f73,f42])).

fof(f42,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f80,plain,
    ( ~ spl3_10
    | spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f75,f68,f45,f77])).

fof(f45,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_3
    | ~ spl3_8 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f74,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f72])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f70,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f30,f68])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f61,f58,f35,f63])).

fof(f35,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f58,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f59,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f58])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f28,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f52,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f21,f50])).

fof(f48,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f38,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:07:45 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.43  % (30902)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.43  % (30902)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f169,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f38,f43,f48,f52,f56,f60,f66,f70,f74,f80,f87,f91,f108,f114,f150,f162])).
% 0.22/0.43  fof(f162,plain,(
% 0.22/0.43    ~spl3_4 | ~spl3_5 | spl3_10 | ~spl3_13 | ~spl3_15),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f161])).
% 0.22/0.43  fof(f161,plain,(
% 0.22/0.43    $false | (~spl3_4 | ~spl3_5 | spl3_10 | ~spl3_13 | ~spl3_15)),
% 0.22/0.43    inference(subsumption_resolution,[],[f160,f79])).
% 0.22/0.43  fof(f79,plain,(
% 0.22/0.43    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_10),
% 0.22/0.43    inference(avatar_component_clause,[],[f77])).
% 0.22/0.43  fof(f77,plain,(
% 0.22/0.43    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.43  fof(f160,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_13 | ~spl3_15)),
% 0.22/0.43    inference(forward_demodulation,[],[f159,f55])).
% 0.22/0.43  fof(f55,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_5),
% 0.22/0.43    inference(avatar_component_clause,[],[f54])).
% 0.22/0.43  fof(f54,plain,(
% 0.22/0.43    spl3_5 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.43  fof(f159,plain,(
% 0.22/0.43    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,sK0) | (~spl3_4 | ~spl3_5 | ~spl3_13 | ~spl3_15)),
% 0.22/0.43    inference(forward_demodulation,[],[f158,f51])).
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.22/0.43    inference(avatar_component_clause,[],[f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.43  fof(f158,plain,(
% 0.22/0.43    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) | (~spl3_5 | ~spl3_13 | ~spl3_15)),
% 0.22/0.43    inference(forward_demodulation,[],[f151,f55])).
% 0.22/0.43  fof(f151,plain,(
% 0.22/0.43    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))) | (~spl3_13 | ~spl3_15)),
% 0.22/0.43    inference(superposition,[],[f149,f107])).
% 0.22/0.43  fof(f107,plain,(
% 0.22/0.43    sK1 = k4_xboole_0(sK1,sK2) | ~spl3_13),
% 0.22/0.43    inference(avatar_component_clause,[],[f105])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    spl3_13 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.43  fof(f149,plain,(
% 0.22/0.43    ( ! [X11] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X11))) ) | ~spl3_15),
% 0.22/0.43    inference(avatar_component_clause,[],[f148])).
% 0.22/0.43  fof(f148,plain,(
% 0.22/0.43    spl3_15 <=> ! [X11] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X11))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.43  fof(f150,plain,(
% 0.22/0.43    spl3_15 | ~spl3_4 | ~spl3_7 | ~spl3_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f135,f112,f63,f50,f148])).
% 0.22/0.43  fof(f63,plain,(
% 0.22/0.43    spl3_7 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.43  fof(f112,plain,(
% 0.22/0.43    spl3_14 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.43  fof(f135,plain,(
% 0.22/0.43    ( ! [X11] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X11))) ) | (~spl3_4 | ~spl3_7 | ~spl3_14)),
% 0.22/0.43    inference(forward_demodulation,[],[f119,f51])).
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    ( ! [X11] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X11)))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X11))) ) | (~spl3_7 | ~spl3_14)),
% 0.22/0.43    inference(superposition,[],[f113,f65])).
% 0.22/0.43  fof(f65,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_7),
% 0.22/0.43    inference(avatar_component_clause,[],[f63])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) ) | ~spl3_14),
% 0.22/0.43    inference(avatar_component_clause,[],[f112])).
% 0.22/0.43  fof(f114,plain,(
% 0.22/0.43    spl3_14),
% 0.22/0.43    inference(avatar_split_clause,[],[f32,f112])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f27,f23,f23,f23,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.43  fof(f108,plain,(
% 0.22/0.43    spl3_13 | ~spl3_4 | ~spl3_11 | ~spl3_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f102,f89,f84,f50,f105])).
% 0.22/0.43  fof(f84,plain,(
% 0.22/0.43    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    spl3_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.43  fof(f102,plain,(
% 0.22/0.43    sK1 = k4_xboole_0(sK1,sK2) | (~spl3_4 | ~spl3_11 | ~spl3_12)),
% 0.22/0.43    inference(forward_demodulation,[],[f97,f51])).
% 0.22/0.43  fof(f97,plain,(
% 0.22/0.43    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_xboole_0) | (~spl3_11 | ~spl3_12)),
% 0.22/0.43    inference(superposition,[],[f90,f86])).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl3_11),
% 0.22/0.43    inference(avatar_component_clause,[],[f84])).
% 0.22/0.43  fof(f90,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_12),
% 0.22/0.43    inference(avatar_component_clause,[],[f89])).
% 0.22/0.43  fof(f91,plain,(
% 0.22/0.43    spl3_12),
% 0.22/0.43    inference(avatar_split_clause,[],[f29,f89])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.43    inference(definition_unfolding,[],[f22,f23])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,axiom,(
% 0.22/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    spl3_11 | ~spl3_2 | ~spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f81,f72,f40,f84])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    spl3_2 <=> r1_xboole_0(sK1,sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.43  fof(f72,plain,(
% 0.22/0.43    spl3_9 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.43  fof(f81,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | (~spl3_2 | ~spl3_9)),
% 0.22/0.43    inference(resolution,[],[f73,f42])).
% 0.22/0.43  fof(f42,plain,(
% 0.22/0.43    r1_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f40])).
% 0.22/0.43  fof(f73,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_9),
% 0.22/0.43    inference(avatar_component_clause,[],[f72])).
% 0.22/0.43  fof(f80,plain,(
% 0.22/0.43    ~spl3_10 | spl3_3 | ~spl3_8),
% 0.22/0.43    inference(avatar_split_clause,[],[f75,f68,f45,f77])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.43  fof(f68,plain,(
% 0.22/0.43    spl3_8 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.43  fof(f75,plain,(
% 0.22/0.43    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (spl3_3 | ~spl3_8)),
% 0.22/0.43    inference(resolution,[],[f69,f47])).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    ~r1_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.43    inference(avatar_component_clause,[],[f45])).
% 0.22/0.43  fof(f69,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_8),
% 0.22/0.43    inference(avatar_component_clause,[],[f68])).
% 0.22/0.43  fof(f74,plain,(
% 0.22/0.43    spl3_9),
% 0.22/0.43    inference(avatar_split_clause,[],[f31,f72])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f24,f23])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(nnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.44  fof(f70,plain,(
% 0.22/0.44    spl3_8),
% 0.22/0.44    inference(avatar_split_clause,[],[f30,f68])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f25,f23])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f16])).
% 0.22/0.44  fof(f66,plain,(
% 0.22/0.44    spl3_7 | ~spl3_1 | ~spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f61,f58,f35,f63])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    spl3_6 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.44  fof(f61,plain,(
% 0.22/0.44    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_6)),
% 0.22/0.44    inference(resolution,[],[f59,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f35])).
% 0.22/0.44  fof(f59,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.22/0.44    inference(avatar_component_clause,[],[f58])).
% 0.22/0.44  fof(f60,plain,(
% 0.22/0.44    spl3_6),
% 0.22/0.44    inference(avatar_split_clause,[],[f26,f58])).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.22/0.44    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.44  fof(f56,plain,(
% 0.22/0.44    spl3_5),
% 0.22/0.44    inference(avatar_split_clause,[],[f33,f54])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.44    inference(backward_demodulation,[],[f28,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f20,f23])).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_4),
% 0.22/0.44    inference(avatar_split_clause,[],[f21,f50])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ~spl3_3),
% 0.22/0.44    inference(avatar_split_clause,[],[f19,f45])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.22/0.44    inference(flattening,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.44    inference(negated_conjecture,[],[f8])).
% 0.22/0.44  fof(f8,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    spl3_2),
% 0.22/0.44    inference(avatar_split_clause,[],[f18,f40])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    r1_xboole_0(sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f17,f35])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (30902)------------------------------
% 0.22/0.44  % (30902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (30902)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (30902)Memory used [KB]: 6140
% 0.22/0.44  % (30902)Time elapsed: 0.010 s
% 0.22/0.44  % (30902)------------------------------
% 0.22/0.44  % (30902)------------------------------
% 0.22/0.44  % (30894)Success in time 0.069 s
%------------------------------------------------------------------------------
