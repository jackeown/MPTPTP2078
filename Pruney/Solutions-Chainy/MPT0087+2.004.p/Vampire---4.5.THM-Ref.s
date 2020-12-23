%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 140 expanded)
%              Number of leaves         :   27 (  68 expanded)
%              Depth                    :    6
%              Number of atoms          :  183 ( 281 expanded)
%              Number of equality atoms :   56 (  96 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f43,f47,f51,f59,f67,f88,f97,f120,f183,f187,f198,f235,f277,f291,f365,f378])).

fof(f378,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl3_2
    | ~ spl3_4
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f38,f368])).

fof(f368,plain,
    ( ! [X0] : r1_xboole_0(sK0,k4_xboole_0(sK1,X0))
    | ~ spl3_4
    | ~ spl3_32 ),
    inference(superposition,[],[f46,f364])).

fof(f364,plain,
    ( ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X9))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl3_32
  <=> ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f46,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f365,plain,
    ( spl3_32
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f342,f289,f195,f185,f363])).

fof(f185,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f195,plain,
    ( spl3_24
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f289,plain,
    ( spl3_30
  <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f342,plain,
    ( ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X9))
    | ~ spl3_23
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f319,f290])).

fof(f290,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f289])).

fof(f319,plain,
    ( ! [X9] : k4_xboole_0(sK0,k4_xboole_0(sK1,X9)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X9)))
    | ~ spl3_23
    | ~ spl3_24 ),
    inference(superposition,[],[f186,f197])).

fof(f197,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f195])).

fof(f186,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f291,plain,
    ( spl3_30
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f282,f275,f49,f289])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f275,plain,
    ( spl3_29
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f282,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl3_5
    | ~ spl3_29 ),
    inference(superposition,[],[f276,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f276,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( spl3_29
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f262,f233,f65,f275])).

fof(f65,plain,
    ( spl3_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f233,plain,
    ( spl3_28
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f262,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2
    | ~ spl3_7
    | ~ spl3_28 ),
    inference(superposition,[],[f234,f66])).

fof(f66,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f65])).

fof(f234,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f233])).

fof(f235,plain,
    ( spl3_28
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f171,f95,f49,f233])).

fof(f95,plain,
    ( spl3_12
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f171,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f96,f50])).

fof(f96,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f198,plain,
    ( spl3_24
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f188,f180,f57,f195])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f180,plain,
    ( spl3_22
  <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f188,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_22 ),
    inference(superposition,[],[f182,f58])).

fof(f58,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f182,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f187,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f29,f185])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f183,plain,
    ( spl3_22
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f165,f117,f95,f180])).

fof(f117,plain,
    ( spl3_16
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f165,plain,
    ( sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f96,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f120,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f90,f86,f31,f117])).

fof(f31,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f86,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f90,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(resolution,[],[f87,f33])).

fof(f33,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f86])).

fof(f97,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f26,f95])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f88,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f86])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f67,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f21,f65])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f59,plain,
    ( spl3_6
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f52,f49,f41,f57])).

fof(f41,plain,
    ( spl3_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f52,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f50,f42])).

fof(f42,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f51,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f19,f49])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f43,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f39,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f16,f36])).

fof(f16,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:11:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (24732)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (24734)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (24735)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (24740)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (24736)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (24736)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (24741)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (24746)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (24745)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (24744)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (24743)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (24731)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (24728)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (24737)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (24729)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (24733)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (24742)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f34,f39,f43,f47,f51,f59,f67,f88,f97,f120,f183,f187,f198,f235,f277,f291,f365,f378])).
% 0.21/0.48  fof(f378,plain,(
% 0.21/0.48    spl3_2 | ~spl3_4 | ~spl3_32),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f377])).
% 0.21/0.48  fof(f377,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_4 | ~spl3_32)),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f368])).
% 0.21/0.48  fof(f368,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(sK1,X0))) ) | (~spl3_4 | ~spl3_32)),
% 0.21/0.48    inference(superposition,[],[f46,f364])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    ( ! [X9] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X9))) ) | ~spl3_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f363])).
% 0.21/0.48  fof(f363,plain,(
% 0.21/0.48    spl3_32 <=> ! [X9] : sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X9))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl3_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl3_2 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    spl3_32 | ~spl3_23 | ~spl3_24 | ~spl3_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f342,f289,f195,f185,f363])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    spl3_23 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl3_24 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    spl3_30 <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f342,plain,(
% 0.21/0.48    ( ! [X9] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,X9))) ) | (~spl3_23 | ~spl3_24 | ~spl3_30)),
% 0.21/0.48    inference(forward_demodulation,[],[f319,f290])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | ~spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f289])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    ( ! [X9] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X9)) = k2_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X9)))) ) | (~spl3_23 | ~spl3_24)),
% 0.21/0.48    inference(superposition,[],[f186,f197])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,sK1) | ~spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f185])).
% 0.21/0.48  fof(f291,plain,(
% 0.21/0.48    spl3_30 | ~spl3_5 | ~spl3_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f282,f275,f49,f289])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    spl3_29 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | (~spl3_5 | ~spl3_29)),
% 0.21/0.48    inference(superposition,[],[f276,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) ) | ~spl3_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f275])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    spl3_29 | ~spl3_7 | ~spl3_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f262,f233,f65,f275])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    spl3_28 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) ) | (~spl3_7 | ~spl3_28)),
% 0.21/0.48    inference(superposition,[],[f234,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f234,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | ~spl3_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f233])).
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    spl3_28 | ~spl3_5 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f171,f95,f49,f233])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) ) | (~spl3_5 | ~spl3_12)),
% 0.21/0.48    inference(superposition,[],[f96,f50])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl3_24 | ~spl3_6 | ~spl3_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f188,f180,f57,f195])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_6 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl3_22 <=> sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    sK0 = k4_xboole_0(sK0,sK1) | (~spl3_6 | ~spl3_22)),
% 0.21/0.48    inference(superposition,[],[f182,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f180])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f185])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    spl3_22 | ~spl3_12 | ~spl3_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f165,f117,f95,f180])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    spl3_16 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.48  fof(f165,plain,(
% 0.21/0.48    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) | (~spl3_12 | ~spl3_16)),
% 0.21/0.48    inference(superposition,[],[f96,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f117])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl3_16 | ~spl3_1 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f90,f86,f31,f117])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_11 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_11)),
% 0.21/0.48    inference(resolution,[],[f87,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f31])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f95])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f20])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f86])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f20])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f65])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_6 | ~spl3_3 | ~spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f49,f41,f57])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_3 | ~spl3_5)),
% 0.21/0.48    inference(superposition,[],[f50,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f49])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f41])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r1_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (24736)------------------------------
% 0.21/0.48  % (24736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24736)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (24736)Memory used [KB]: 6268
% 0.21/0.48  % (24736)Time elapsed: 0.034 s
% 0.21/0.48  % (24736)------------------------------
% 0.21/0.48  % (24736)------------------------------
% 0.21/0.49  % (24727)Success in time 0.129 s
%------------------------------------------------------------------------------
