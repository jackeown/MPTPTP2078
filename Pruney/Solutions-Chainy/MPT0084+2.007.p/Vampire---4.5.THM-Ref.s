%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 173 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  132 ( 277 expanded)
%              Number of equality atoms :   47 ( 112 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1276,f1279,f1283])).

fof(f1283,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f1282])).

fof(f1282,plain,
    ( $false
    | ~ spl5_6 ),
    inference(resolution,[],[f1275,f78])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f77,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f48,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f77,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f75,f34])).

fof(f75,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1275,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f1273])).

fof(f1273,plain,
    ( spl5_6
  <=> r2_hidden(sK4(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f1279,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1277])).

fof(f1277,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f1271,f29])).

fof(f29,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f1271,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f1269])).

fof(f1269,plain,
    ( spl5_5
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1276,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f992,f1273,f1269])).

fof(f992,plain,
    ( r2_hidden(sK4(sK0,sK1),k1_xboole_0)
    | r1_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f983,f56])).

fof(f983,plain,
    ( r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK0))
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f52,f929])).

fof(f929,plain,(
    sK0 = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f726,f95])).

fof(f95,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f89,f34])).

fof(f89,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f49,f80])).

fof(f80,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f76,plain,(
    ! [X2] : ~ r2_hidden(X2,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f31,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f726,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,X12) = k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) ),
    inference(forward_demodulation,[],[f725,f110])).

fof(f110,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f101,f56])).

fof(f101,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[],[f50,f34])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f725,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X12)) ),
    inference(forward_demodulation,[],[f724,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f724,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k1_xboole_0) ),
    inference(forward_demodulation,[],[f710,f56])).

fof(f710,plain,(
    ! [X12,X11] : k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f55,f657])).

fof(f657,plain,(
    ! [X13] : sK0 = k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) ),
    inference(forward_demodulation,[],[f656,f155])).

fof(f155,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f144,f36])).

fof(f144,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f100,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f100,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[],[f50,f49])).

fof(f656,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(sK0,k4_xboole_0(sK0,X13)) ),
    inference(forward_demodulation,[],[f655,f36])).

fof(f655,plain,(
    ! [X13] : k2_xboole_0(k4_xboole_0(sK0,X13),sK0) = k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) ),
    inference(forward_demodulation,[],[f600,f34])).

fof(f600,plain,(
    ! [X13] : k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X13),k4_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f55,f57])).

fof(f57,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f43,f30])).

fof(f30,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (4359)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (4355)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (4366)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (4358)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (4363)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (4353)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (4368)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (4357)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (4354)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (4355)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1284,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f1276,f1279,f1283])).
% 0.21/0.50  fof(f1283,plain,(
% 0.21/0.50    ~spl5_6),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1282])).
% 0.21/0.50  fof(f1282,plain,(
% 0.21/0.50    $false | ~spl5_6),
% 0.21/0.50    inference(resolution,[],[f1275,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f77,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f48,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f33,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f75,f34])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 0.21/0.50    inference(resolution,[],[f51,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f42,f38])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.50  fof(f1275,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | ~spl5_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f1273])).
% 0.21/0.50  fof(f1273,plain,(
% 0.21/0.50    spl5_6 <=> r2_hidden(sK4(sK0,sK1),k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.50  fof(f1279,plain,(
% 0.21/0.50    ~spl5_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1277])).
% 0.21/0.50  fof(f1277,plain,(
% 0.21/0.50    $false | ~spl5_5),
% 0.21/0.50    inference(resolution,[],[f1271,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.21/0.50  fof(f1271,plain,(
% 0.21/0.50    r1_xboole_0(sK0,sK1) | ~spl5_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f1269])).
% 0.21/0.50  fof(f1269,plain,(
% 0.21/0.50    spl5_5 <=> r1_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.50  fof(f1276,plain,(
% 0.21/0.50    spl5_5 | spl5_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f992,f1273,f1269])).
% 0.21/0.50  fof(f992,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1),k1_xboole_0) | r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(forward_demodulation,[],[f983,f56])).
% 0.21/0.50  fof(f983,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1),k4_xboole_0(sK0,sK0)) | r1_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(superposition,[],[f52,f929])).
% 0.21/0.50  fof(f929,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(superposition,[],[f726,f95])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.50    inference(forward_demodulation,[],[f89,f34])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.50    inference(superposition,[],[f49,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.21/0.50    inference(resolution,[],[f76,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))))) )),
% 0.21/0.50    inference(resolution,[],[f51,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.21/0.50    inference(definition_unfolding,[],[f31,f38])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f39,f38])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.50  fof(f726,plain,(
% 0.21/0.50    ( ! [X12,X11] : (k4_xboole_0(sK0,X12) = k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f725,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.50    inference(forward_demodulation,[],[f101,f56])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0) )),
% 0.21/0.50    inference(superposition,[],[f50,f34])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f40,f38])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.50  fof(f725,plain,(
% 0.21/0.50    ( ! [X12,X11] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,X12))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f724,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.50  fof(f724,plain,(
% 0.21/0.50    ( ! [X12,X11] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k1_xboole_0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f710,f56])).
% 0.21/0.50  fof(f710,plain,(
% 0.21/0.50    ( ! [X12,X11] : (k4_xboole_0(sK0,k4_xboole_0(X12,k4_xboole_0(X11,sK2))) = k2_xboole_0(k4_xboole_0(sK0,X12),k4_xboole_0(sK0,sK0))) )),
% 0.21/0.50    inference(superposition,[],[f55,f657])).
% 0.21/0.50  fof(f657,plain,(
% 0.21/0.50    ( ! [X13] : (sK0 = k4_xboole_0(sK0,k4_xboole_0(X13,sK2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f656,f155])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 0.21/0.50    inference(superposition,[],[f144,f36])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 0.21/0.50    inference(superposition,[],[f100,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.21/0.50    inference(superposition,[],[f50,f49])).
% 0.21/0.50  fof(f656,plain,(
% 0.21/0.50    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(sK0,k4_xboole_0(sK0,X13))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f655,f36])).
% 0.21/0.50  fof(f655,plain,(
% 0.21/0.50    ( ! [X13] : (k2_xboole_0(k4_xboole_0(sK0,X13),sK0) = k4_xboole_0(sK0,k4_xboole_0(X13,sK2))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f600,f34])).
% 0.21/0.50  fof(f600,plain,(
% 0.21/0.50    ( ! [X13] : (k4_xboole_0(sK0,k4_xboole_0(X13,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X13),k4_xboole_0(sK0,k1_xboole_0))) )),
% 0.21/0.50    inference(superposition,[],[f55,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(resolution,[],[f43,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    r1_tarski(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.21/0.50    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f46,f38])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f41,f38])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4355)------------------------------
% 0.21/0.50  % (4355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4355)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4355)Memory used [KB]: 6652
% 0.21/0.50  % (4355)Time elapsed: 0.069 s
% 0.21/0.50  % (4355)------------------------------
% 0.21/0.50  % (4355)------------------------------
% 0.21/0.50  % (4352)Success in time 0.14 s
%------------------------------------------------------------------------------
