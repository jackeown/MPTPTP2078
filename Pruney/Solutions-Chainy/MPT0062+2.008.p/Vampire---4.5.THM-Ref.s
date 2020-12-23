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
% DateTime   : Thu Dec  3 12:30:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :  120 ( 178 expanded)
%              Number of equality atoms :   48 (  78 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f28,f32,f36,f59,f71,f75,f140,f158])).

fof(f158,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f19,f156])).

fof(f156,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X6),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X4))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f91,f155])).

fof(f155,plain,
    ( ! [X6,X4,X5] : k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X4))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f63,f153])).

fof(f153,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X6,X4),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X4))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f89,f152])).

fof(f152,plain,
    ( ! [X6,X8,X7] : k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,X7))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f143,f139])).

fof(f139,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f143,plain,
    ( ! [X6,X8,X7] : k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,k2_xboole_0(X6,X7)))
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(superposition,[],[f139,f27])).

fof(f27,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f89,plain,
    ( ! [X6,X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(k2_xboole_0(X6,X4),k4_xboole_0(X4,k4_xboole_0(X4,X5)))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f74,f35])).

fof(f35,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_4
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f74,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_7
  <=> ! [X3,X5,X4] : k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f63,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X6,X4),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f58,f35])).

fof(f58,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_5
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f91,plain,
    ( ! [X6,X4,X5] : k4_xboole_0(k2_xboole_0(X4,X6),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f74,f35])).

fof(f19,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f12,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f140,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f76,f69,f22,f138])).

fof(f22,plain,
    ( spl2_1
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f69,plain,
    ( spl2_6
  <=> ! [X1,X0,X2] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f76,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(superposition,[],[f70,f23])).

fof(f23,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f70,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f75,plain,
    ( spl2_7
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f64,f57,f22,f73])).

fof(f64,plain,
    ( ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f58,f23])).

fof(f71,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f38,f30,f26,f69])).

fof(f30,plain,
    ( spl2_3
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f38,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f27,f31])).

fof(f31,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f18,f57])).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f36,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f32,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f30])).

fof(f17,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f28,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f24,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f13,f22])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n020.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:47:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (19552)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.42  % (19552)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f162,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f24,f28,f32,f36,f59,f71,f75,f140,f158])).
% 0.22/0.42  fof(f158,plain,(
% 0.22/0.42    ~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_9),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f157])).
% 0.22/0.42  fof(f157,plain,(
% 0.22/0.42    $false | (~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.22/0.42    inference(subsumption_resolution,[],[f19,f156])).
% 0.22/0.42  fof(f156,plain,(
% 0.22/0.42    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X6),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X4))) ) | (~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.22/0.42    inference(backward_demodulation,[],[f91,f155])).
% 0.22/0.42  fof(f155,plain,(
% 0.22/0.42    ( ! [X6,X4,X5] : (k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X4))) ) | (~spl2_2 | ~spl2_4 | ~spl2_5 | ~spl2_7 | ~spl2_9)),
% 0.22/0.42    inference(backward_demodulation,[],[f63,f153])).
% 0.22/0.42  fof(f153,plain,(
% 0.22/0.42    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X6,X4),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,X4))) ) | (~spl2_2 | ~spl2_4 | ~spl2_7 | ~spl2_9)),
% 0.22/0.42    inference(backward_demodulation,[],[f89,f152])).
% 0.22/0.42  fof(f152,plain,(
% 0.22/0.42    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,X7))) ) | (~spl2_2 | ~spl2_9)),
% 0.22/0.42    inference(forward_demodulation,[],[f143,f139])).
% 0.22/0.42  fof(f139,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) ) | ~spl2_9),
% 0.22/0.42    inference(avatar_component_clause,[],[f138])).
% 0.22/0.42  fof(f138,plain,(
% 0.22/0.42    spl2_9 <=> ! [X1,X0,X2] : k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.42  fof(f143,plain,(
% 0.22/0.42    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k4_xboole_0(X8,k4_xboole_0(X7,X6))) = k2_xboole_0(X6,k4_xboole_0(X8,k2_xboole_0(X6,X7)))) ) | (~spl2_2 | ~spl2_9)),
% 0.22/0.42    inference(superposition,[],[f139,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    spl2_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f89,plain,(
% 0.22/0.42    ( ! [X6,X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5)))) = k4_xboole_0(k2_xboole_0(X6,X4),k4_xboole_0(X4,k4_xboole_0(X4,X5)))) ) | (~spl2_4 | ~spl2_7)),
% 0.22/0.42    inference(superposition,[],[f74,f35])).
% 0.22/0.42  fof(f35,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    spl2_4 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)) ) | ~spl2_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    spl2_7 <=> ! [X3,X5,X4] : k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.42  fof(f63,plain,(
% 0.22/0.42    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X6,X4),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_5)),
% 0.22/0.42    inference(superposition,[],[f58,f35])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl2_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f57])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl2_5 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.42  fof(f91,plain,(
% 0.22/0.42    ( ! [X6,X4,X5] : (k4_xboole_0(k2_xboole_0(X4,X6),k4_xboole_0(X4,k4_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(X6,k4_xboole_0(X4,k4_xboole_0(X4,X5))),k4_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_7)),
% 0.22/0.42    inference(superposition,[],[f74,f35])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.22/0.42    inference(definition_unfolding,[],[f12,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.42    inference(negated_conjecture,[],[f7])).
% 0.22/0.42  fof(f7,conjecture,(
% 0.22/0.42    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 0.22/0.42  fof(f140,plain,(
% 0.22/0.42    spl2_9 | ~spl2_1 | ~spl2_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f76,f69,f22,f138])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    spl2_1 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    spl2_6 <=> ! [X1,X0,X2] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.42  fof(f76,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(X1,k4_xboole_0(X2,X0)) = k2_xboole_0(X1,k4_xboole_0(X2,k2_xboole_0(X1,X0)))) ) | (~spl2_1 | ~spl2_6)),
% 0.22/0.42    inference(superposition,[],[f70,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f22])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ) | ~spl2_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f69])).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    spl2_7 | ~spl2_1 | ~spl2_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f64,f57,f22,f73])).
% 0.22/0.42  fof(f64,plain,(
% 0.22/0.42    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)) ) | (~spl2_1 | ~spl2_5)),
% 0.22/0.42    inference(superposition,[],[f58,f23])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    spl2_6 | ~spl2_2 | ~spl2_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f38,f30,f26,f69])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    spl2_3 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.42    inference(superposition,[],[f27,f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f30])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl2_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f57])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    spl2_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f34])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.22/0.42    inference(definition_unfolding,[],[f16,f14])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    spl2_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f30])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f15,f26])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    spl2_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f13,f22])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (19552)------------------------------
% 0.22/0.42  % (19552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (19552)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (19552)Memory used [KB]: 6268
% 0.22/0.42  % (19552)Time elapsed: 0.011 s
% 0.22/0.42  % (19552)------------------------------
% 0.22/0.42  % (19552)------------------------------
% 0.22/0.43  % (19544)Success in time 0.068 s
%------------------------------------------------------------------------------
