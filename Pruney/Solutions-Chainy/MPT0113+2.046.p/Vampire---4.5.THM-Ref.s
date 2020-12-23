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
% DateTime   : Thu Dec  3 12:32:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 131 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  129 ( 235 expanded)
%              Number of equality atoms :   34 (  81 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1598,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f83,f101,f174,f503,f764,f852,f1562])).

fof(f1562,plain,
    ( spl3_1
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f1519,f847,f43])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f847,plain,
    ( spl3_26
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1519,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_26 ),
    inference(superposition,[],[f121,f849])).

fof(f849,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f847])).

fof(f121,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5) ),
    inference(superposition,[],[f26,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f852,plain,
    ( spl3_26
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f851,f761,f847])).

fof(f761,plain,
    ( spl3_23
  <=> r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f851,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f838,f133])).

fof(f133,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f40,f37])).

fof(f37,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f30])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f34,f30,f30])).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f838,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl3_23 ),
    inference(resolution,[],[f763,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f763,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f761])).

fof(f764,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f759,f171,f79,f761])).

fof(f79,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f171,plain,
    ( spl3_9
  <=> sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f759,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f722,f173])).

fof(f173,plain,
    ( sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f171])).

fof(f722,plain,
    ( r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f145,f81])).

fof(f81,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f145,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))),k4_xboole_0(X11,k4_xboole_0(X11,X12))) ),
    inference(superposition,[],[f26,f40])).

fof(f503,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f502,f171,f79,f47])).

fof(f47,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f502,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f495,f173])).

fof(f495,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f146,f81])).

fof(f146,plain,(
    ! [X14,X15,X16] : r1_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))),X16) ),
    inference(superposition,[],[f25,f40])).

fof(f25,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f174,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f169,f96,f79,f171])).

fof(f96,plain,
    ( spl3_6
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f169,plain,
    ( sK0 = k4_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f98,f81])).

fof(f98,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f101,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f94,f52,f96])).

fof(f52,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f94,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f83,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f77,f52,f79])).

fof(f77,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f33,f54])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f52])).

fof(f21,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f50,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f22,f47,f43])).

fof(f22,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 20:35:30 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.41  % (22726)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.45  % (22726)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f1598,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f50,f55,f83,f101,f174,f503,f764,f852,f1562])).
% 0.21/0.45  fof(f1562,plain,(
% 0.21/0.45    spl3_1 | ~spl3_26),
% 0.21/0.45    inference(avatar_split_clause,[],[f1519,f847,f43])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f847,plain,(
% 0.21/0.45    spl3_26 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.45  fof(f1519,plain,(
% 0.21/0.45    r1_tarski(sK0,sK1) | ~spl3_26),
% 0.21/0.45    inference(superposition,[],[f121,f849])).
% 0.21/0.45  fof(f849,plain,(
% 0.21/0.45    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f847])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(X6,k4_xboole_0(X6,X5)),X5)) )),
% 0.21/0.45    inference(superposition,[],[f26,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.45    inference(definition_unfolding,[],[f28,f30,f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.46  fof(f852,plain,(
% 0.21/0.46    spl3_26 | ~spl3_23),
% 0.21/0.46    inference(avatar_split_clause,[],[f851,f761,f847])).
% 0.21/0.46  fof(f761,plain,(
% 0.21/0.46    spl3_23 <=> r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.46  fof(f851,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_23),
% 0.21/0.46    inference(forward_demodulation,[],[f838,f133])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.46    inference(superposition,[],[f40,f37])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f24,f30])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    inference(rectify,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.21/0.46    inference(definition_unfolding,[],[f34,f30,f30])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.46  fof(f838,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~spl3_23),
% 0.21/0.46    inference(resolution,[],[f763,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.46    inference(definition_unfolding,[],[f31,f30])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f763,plain,(
% 0.21/0.46    r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl3_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f761])).
% 0.21/0.46  fof(f764,plain,(
% 0.21/0.46    spl3_23 | ~spl3_5 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f759,f171,f79,f761])).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    spl3_9 <=> sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f759,plain,(
% 0.21/0.46    r1_tarski(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | (~spl3_5 | ~spl3_9)),
% 0.21/0.46    inference(forward_demodulation,[],[f722,f173])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,k1_xboole_0) | ~spl3_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f171])).
% 0.21/0.46  fof(f722,plain,(
% 0.21/0.46    r1_tarski(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl3_5),
% 0.21/0.46    inference(superposition,[],[f145,f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f79])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))),k4_xboole_0(X11,k4_xboole_0(X11,X12)))) )),
% 0.21/0.46    inference(superposition,[],[f26,f40])).
% 0.21/0.46  fof(f503,plain,(
% 0.21/0.46    spl3_2 | ~spl3_5 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f502,f171,f79,f47])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f502,plain,(
% 0.21/0.46    r1_xboole_0(sK0,sK2) | (~spl3_5 | ~spl3_9)),
% 0.21/0.46    inference(forward_demodulation,[],[f495,f173])).
% 0.21/0.46  fof(f495,plain,(
% 0.21/0.46    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK2) | ~spl3_5),
% 0.21/0.46    inference(superposition,[],[f146,f81])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    ( ! [X14,X15,X16] : (r1_xboole_0(k4_xboole_0(X14,k4_xboole_0(X14,k4_xboole_0(X15,X16))),X16)) )),
% 0.21/0.46    inference(superposition,[],[f25,f40])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.46    spl3_9 | ~spl3_5 | ~spl3_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f169,f96,f79,f171])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    spl3_6 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f169,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,k1_xboole_0) | (~spl3_5 | ~spl3_6)),
% 0.21/0.46    inference(forward_demodulation,[],[f98,f81])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f96])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_6 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f94,f52,f96])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    spl3_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.21/0.46    inference(resolution,[],[f39,f54])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl3_5 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f77,f52,f79])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.21/0.46    inference(resolution,[],[f33,f54])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.46    inference(nnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f52])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.46    inference(negated_conjecture,[],[f13])).
% 0.21/0.46  fof(f13,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    ~spl3_1 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f47,f43])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (22726)------------------------------
% 0.21/0.46  % (22726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (22726)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (22726)Memory used [KB]: 7419
% 0.21/0.46  % (22726)Time elapsed: 0.044 s
% 0.21/0.46  % (22726)------------------------------
% 0.21/0.46  % (22726)------------------------------
% 0.21/0.46  % (22719)Success in time 0.102 s
%------------------------------------------------------------------------------
