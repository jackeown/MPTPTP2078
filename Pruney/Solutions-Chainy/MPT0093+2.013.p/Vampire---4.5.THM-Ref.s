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
% DateTime   : Thu Dec  3 12:31:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 127 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  177 ( 293 expanded)
%              Number of equality atoms :   50 (  80 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f55,f59,f63,f69,f75,f82,f86,f107,f115])).

fof(f115,plain,
    ( spl3_10
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl3_10
    | ~ spl3_11
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f109,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f109,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_10
    | ~ spl3_13 ),
    inference(superposition,[],[f74,f106])).

fof(f106,plain,
    ( ! [X4] : k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_13
  <=> ! [X4] : k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f74,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_10
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f107,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f101,f84,f66,f49,f45,f105])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( spl3_9
  <=> sK0 = k4_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f84,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f101,plain,
    ( ! [X4] : k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f100,f98])).

fof(f98,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f97,f46])).

fof(f46,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f97,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f91,f50])).

fof(f50,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f91,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f85,f46])).

fof(f85,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f100,plain,
    ( ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X4),k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f93,f50])).

fof(f93,plain,
    ( ! [X4] : k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X4),k4_xboole_0(sK0,sK0))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f85,f68])).

fof(f68,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f86,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f27,f84])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f82,plain,
    ( spl3_11
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f76,f61,f30,f79])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f76,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(resolution,[],[f62,f32])).

fof(f32,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f75,plain,
    ( ~ spl3_10
    | spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f70,f57,f40,f72])).

fof(f40,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f57,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f70,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_3
    | ~ spl3_7 ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f69,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f64,f53,f35,f66])).

fof(f35,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f53,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f64,plain,
    ( sK0 = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f63,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f59,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f57])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f53])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f26,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f45])).

fof(f43,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f18,f40])).

fof(f18,plain,(
    ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) )
       => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (19122)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.42  % (19122)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f120,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f51,f55,f59,f63,f69,f75,f82,f86,f107,f115])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    spl3_10 | ~spl3_11 | ~spl3_13),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f114])).
% 0.21/0.43  fof(f114,plain,(
% 0.21/0.43    $false | (spl3_10 | ~spl3_11 | ~spl3_13)),
% 0.21/0.43    inference(subsumption_resolution,[],[f109,f81])).
% 0.21/0.43  fof(f81,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f79])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.43  fof(f109,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_10 | ~spl3_13)),
% 0.21/0.43    inference(superposition,[],[f74,f106])).
% 0.21/0.43  fof(f106,plain,(
% 0.21/0.43    ( ! [X4] : (k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK2))) ) | ~spl3_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f105])).
% 0.21/0.43  fof(f105,plain,(
% 0.21/0.43    spl3_13 <=> ! [X4] : k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f72])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    spl3_10 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f107,plain,(
% 0.21/0.43    spl3_13 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f101,f84,f66,f49,f45,f105])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl3_4 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl3_5 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl3_9 <=> sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f101,plain,(
% 0.21/0.43    ( ! [X4] : (k4_xboole_0(sK0,X4) = k4_xboole_0(sK0,k4_xboole_0(X4,sK2))) ) | (~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_12)),
% 0.21/0.43    inference(forward_demodulation,[],[f100,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.21/0.43    inference(forward_demodulation,[],[f97,f46])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f45])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ) | (~spl3_4 | ~spl3_5 | ~spl3_12)),
% 0.21/0.43    inference(forward_demodulation,[],[f91,f50])).
% 0.21/0.43  fof(f50,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f49])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X0))) ) | (~spl3_4 | ~spl3_12)),
% 0.21/0.43    inference(superposition,[],[f85,f46])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f84])).
% 0.21/0.43  fof(f100,plain,(
% 0.21/0.43    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X4),k1_xboole_0)) ) | (~spl3_5 | ~spl3_9 | ~spl3_12)),
% 0.21/0.43    inference(forward_demodulation,[],[f93,f50])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    ( ! [X4] : (k4_xboole_0(sK0,k4_xboole_0(X4,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X4),k4_xboole_0(sK0,sK0))) ) | (~spl3_9 | ~spl3_12)),
% 0.21/0.43    inference(superposition,[],[f85,f68])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    sK0 = k4_xboole_0(sK0,sK2) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f66])).
% 0.21/0.43  fof(f86,plain,(
% 0.21/0.43    spl3_12),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f84])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f25,f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.43  fof(f82,plain,(
% 0.21/0.43    spl3_11 | ~spl3_1 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f76,f61,f30,f79])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f62,f32])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f30])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f61])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ~spl3_10 | spl3_3 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f70,f57,f40,f72])).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    spl3_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl3_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    k1_xboole_0 != k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (spl3_3 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f58,f42])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | spl3_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f40])).
% 0.21/0.43  fof(f58,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f57])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    spl3_9 | ~spl3_2 | ~spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f64,f53,f35,f66])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    sK0 = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_6)),
% 0.21/0.43    inference(resolution,[],[f54,f37])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f35])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f53])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f61])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f57])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f53])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    inference(unused_predicate_definition_removal,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f28,f49])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.43    inference(backward_demodulation,[],[f26,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f19,f21])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f45])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    ~spl3_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f40])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => (~r1_tarski(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X2) & r1_tarski(X0,X1))),
% 0.21/0.43    inference(flattening,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) & (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.43    inference(negated_conjecture,[],[f7])).
% 0.21/0.43  fof(f7,conjecture,(
% 0.21/0.43    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    r1_xboole_0(sK0,sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    r1_tarski(sK0,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (19122)------------------------------
% 0.21/0.43  % (19122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (19122)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (19122)Memory used [KB]: 6140
% 0.21/0.43  % (19122)Time elapsed: 0.006 s
% 0.21/0.43  % (19122)------------------------------
% 0.21/0.43  % (19122)------------------------------
% 0.22/0.43  % (19114)Success in time 0.072 s
%------------------------------------------------------------------------------
