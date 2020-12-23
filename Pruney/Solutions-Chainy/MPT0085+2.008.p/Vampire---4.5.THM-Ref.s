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
% DateTime   : Thu Dec  3 12:31:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 (  96 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  128 ( 186 expanded)
%              Number of equality atoms :   50 (  79 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f47,f67,f73,f94,f98,f102,f257,f279,f284])).

fof(f284,plain,
    ( spl3_11
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | spl3_11
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(trivial_inequality_removal,[],[f282])).

fof(f282,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_11
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(backward_demodulation,[],[f93,f281])).

fof(f281,plain,
    ( ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)
    | ~ spl3_12
    | ~ spl3_27 ),
    inference(superposition,[],[f97,f278])).

fof(f278,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl3_27
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f97,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f93,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_11
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f279,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f258,f254,f45,f276])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f254,plain,
    ( spl3_26
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f258,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_4
    | ~ spl3_26 ),
    inference(superposition,[],[f256,f46])).

fof(f46,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f256,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f254])).

fof(f257,plain,
    ( spl3_26
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f213,f100,f70,f254])).

fof(f70,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f100,plain,
    ( spl3_13
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f213,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(superposition,[],[f101,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f70])).

fof(f101,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f25,f100])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f98,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f23,f96])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f94,plain,(
    ~ spl3_11 ),
    inference(avatar_split_clause,[],[f24,f91])).

% (8649)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
fof(f24,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(definition_unfolding,[],[f16,f19,f19])).

fof(f16,plain,(
    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1) )
   => ( k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f73,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f68,f65,f28,f70])).

fof(f28,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f66,f30])).

fof(f30,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f19])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f47,plain,
    ( spl3_4
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f37,f33,f45])).

fof(f33,plain,
    ( spl3_2
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f37,plain,
    ( spl3_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f40,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f38,f34])).

fof(f34,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f38,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f31,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f28])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:02:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (8655)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.44  % (8655)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f285,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f31,f35,f39,f47,f67,f73,f94,f98,f102,f257,f279,f284])).
% 0.21/0.45  fof(f284,plain,(
% 0.21/0.45    spl3_11 | ~spl3_12 | ~spl3_27),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f283])).
% 0.21/0.45  fof(f283,plain,(
% 0.21/0.45    $false | (spl3_11 | ~spl3_12 | ~spl3_27)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f282])).
% 0.21/0.45  fof(f282,plain,(
% 0.21/0.45    k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | (spl3_11 | ~spl3_12 | ~spl3_27)),
% 0.21/0.45    inference(backward_demodulation,[],[f93,f281])).
% 0.21/0.45  fof(f281,plain,(
% 0.21/0.45    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK0,X0)) ) | (~spl3_12 | ~spl3_27)),
% 0.21/0.45    inference(superposition,[],[f97,f278])).
% 0.21/0.45  fof(f278,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_27),
% 0.21/0.45    inference(avatar_component_clause,[],[f276])).
% 0.21/0.45  fof(f276,plain,(
% 0.21/0.45    spl3_27 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_12),
% 0.21/0.45    inference(avatar_component_clause,[],[f96])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.45  fof(f93,plain,(
% 0.21/0.45    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | spl3_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f91])).
% 0.21/0.45  fof(f91,plain,(
% 0.21/0.45    spl3_11 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.45  fof(f279,plain,(
% 0.21/0.45    spl3_27 | ~spl3_4 | ~spl3_26),
% 0.21/0.45    inference(avatar_split_clause,[],[f258,f254,f45,f276])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    spl3_4 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.45  fof(f254,plain,(
% 0.21/0.45    spl3_26 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.45  fof(f258,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_4 | ~spl3_26)),
% 0.21/0.45    inference(superposition,[],[f256,f46])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f45])).
% 0.21/0.45  fof(f256,plain,(
% 0.21/0.45    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f254])).
% 0.21/0.45  fof(f257,plain,(
% 0.21/0.45    spl3_26 | ~spl3_8 | ~spl3_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f213,f100,f70,f254])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl3_13 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | (~spl3_8 | ~spl3_13)),
% 0.21/0.45    inference(superposition,[],[f101,f72])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl3_13),
% 0.21/0.45    inference(avatar_split_clause,[],[f25,f100])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(definition_unfolding,[],[f21,f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl3_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f23,f96])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.45  fof(f94,plain,(
% 0.21/0.45    ~spl3_11),
% 0.21/0.45    inference(avatar_split_clause,[],[f24,f91])).
% 0.21/0.45  % (8649)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    k4_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.21/0.45    inference(definition_unfolding,[],[f16,f19,f19])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1)) => (k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ? [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(X0,X2) & r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.45    inference(negated_conjecture,[],[f8])).
% 0.21/0.45  fof(f8,conjecture,(
% 0.21/0.45    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f68,f65,f28,f70])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_7 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_7)),
% 0.21/0.45    inference(resolution,[],[f66,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f28])).
% 0.21/0.45  fof(f66,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f65])).
% 0.21/0.45  fof(f67,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f26,f65])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(definition_unfolding,[],[f22,f19])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.45  fof(f47,plain,(
% 0.21/0.45    spl3_4 | ~spl3_2 | ~spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f40,f37,f33,f45])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    spl3_2 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    spl3_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_2 | ~spl3_3)),
% 0.21/0.45    inference(superposition,[],[f38,f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f33])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f37])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f18,f37])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    spl3_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f15,f28])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    r1_xboole_0(sK0,sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f14])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (8655)------------------------------
% 0.21/0.45  % (8655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8655)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (8655)Memory used [KB]: 6268
% 0.21/0.45  % (8655)Time elapsed: 0.011 s
% 0.21/0.45  % (8655)------------------------------
% 0.21/0.45  % (8655)------------------------------
% 0.21/0.45  % (8647)Success in time 0.086 s
%------------------------------------------------------------------------------
