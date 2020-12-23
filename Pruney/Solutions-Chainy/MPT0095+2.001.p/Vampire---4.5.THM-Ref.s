%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 664 expanded)
%              Number of leaves         :   13 ( 190 expanded)
%              Depth                    :   24
%              Number of atoms          :  134 (1056 expanded)
%              Number of equality atoms :   71 ( 631 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f782,f1111,f1236])).

fof(f1236,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f1235])).

fof(f1235,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f1209,f781])).

fof(f781,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f779])).

fof(f779,plain,
    ( spl2_4
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f1209,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) ),
    inference(superposition,[],[f724,f951])).

fof(f951,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f113,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f113,plain,(
    ! [X10] : k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK0,sK1),X10)) = k4_xboole_0(k1_xboole_0,X10) ),
    inference(superposition,[],[f30,f72])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f66,plain,(
    r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f64,f44])).

fof(f44,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | r1_tarski(k1_xboole_0,X9) ) ),
    inference(superposition,[],[f31,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f23,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f64,plain,(
    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f62])).

fof(f62,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f32,f20])).

fof(f20,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
        & r1_xboole_0(X0,X1) )
   => ( sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
       => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f27,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f724,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f722,f30])).

fof(f722,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f719,f29])).

fof(f719,plain,(
    r1_tarski(k4_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f654,f78])).

fof(f78,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f55,f72])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f28,f51])).

fof(f51,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f25,f33])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f654,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(sK0,sK1),X0)
      | r1_tarski(k4_xboole_0(k1_xboole_0,sK0),X0) ) ),
    inference(forward_demodulation,[],[f649,f344])).

fof(f344,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f227,f23])).

fof(f227,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f30,f216])).

fof(f216,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f150,f117])).

fof(f117,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f30,f81])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f78,f29])).

fof(f150,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f116,f23])).

fof(f116,plain,(
    ! [X16] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X16)) = k4_xboole_0(k1_xboole_0,X16) ),
    inference(superposition,[],[f30,f62])).

fof(f649,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)),X0)
      | ~ r1_tarski(k4_xboole_0(sK0,sK1),X0) ) ),
    inference(backward_demodulation,[],[f198,f624])).

fof(f624,plain,(
    ! [X8,X9] : k4_xboole_0(k1_xboole_0,k2_xboole_0(X8,X9)) = k4_xboole_0(X8,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f124,f33])).

fof(f124,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f110,f30])).

fof(f110,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X2,X3),X4) ),
    inference(superposition,[],[f30,f25])).

fof(f198,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(sK0,sK1),X0)
      | r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),X0) ) ),
    inference(superposition,[],[f42,f69])).

fof(f69,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f68,f23])).

fof(f68,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f65,f30])).

fof(f65,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) ),
    inference(resolution,[],[f64,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f42,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X2),X4)
      | r1_tarski(X2,X4) ) ),
    inference(superposition,[],[f31,f23])).

fof(f1111,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f1110])).

fof(f1110,plain,
    ( $false
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f1109,f52])).

fof(f52,plain,(
    sK0 != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f21,f25])).

fof(f21,plain,(
    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f1109,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f1071,f22])).

fof(f1071,plain,
    ( k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f657,f1067])).

fof(f1067,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f656,f1066])).

fof(f1066,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f777,f29])).

fof(f777,plain,
    ( r1_tarski(k4_xboole_0(k1_xboole_0,sK0),sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f775])).

fof(f775,plain,
    ( spl2_3
  <=> r1_tarski(k4_xboole_0(k1_xboole_0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f656,plain,(
    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK0) ),
    inference(forward_demodulation,[],[f651,f344])).

fof(f651,plain,(
    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f201,f624])).

fof(f201,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f200,f23])).

fof(f200,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f196,f30])).

fof(f196,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f49,f69])).

fof(f49,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f25,f23])).

fof(f657,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f652,f344])).

fof(f652,plain,(
    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f69,f624])).

fof(f782,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f678,f779,f775])).

fof(f678,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0)
    | r1_tarski(k4_xboole_0(k1_xboole_0,sK0),sK0) ),
    inference(superposition,[],[f28,f656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (2415)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.44  % (2415)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f1244,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f782,f1111,f1236])).
% 0.21/0.44  fof(f1236,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f1235])).
% 0.21/0.44  fof(f1235,plain,(
% 0.21/0.44    $false | spl2_4),
% 0.21/0.44    inference(subsumption_resolution,[],[f1209,f781])).
% 0.21/0.44  fof(f781,plain,(
% 0.21/0.44    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0) | spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f779])).
% 0.21/0.44  fof(f779,plain,(
% 0.21/0.44    spl2_4 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f1209,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.44    inference(superposition,[],[f724,f951])).
% 0.21/0.44  fof(f951,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1)))) )),
% 0.21/0.44    inference(superposition,[],[f113,f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ( ! [X10] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(sK0,sK1),X10)) = k4_xboole_0(k1_xboole_0,X10)) )),
% 0.21/0.44    inference(superposition,[],[f30,f72])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(resolution,[],[f66,f29])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.44  fof(f66,plain,(
% 0.21/0.44    r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(resolution,[],[f64,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X8,X9] : (~r1_tarski(X8,X9) | r1_tarski(k1_xboole_0,X9)) )),
% 0.21/0.44    inference(superposition,[],[f31,f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.44    inference(superposition,[],[f23,f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f63])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(superposition,[],[f28,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(resolution,[],[f32,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) & r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0 & r1_xboole_0(X0,X1)) => (sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) & r1_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) != X0 & r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.44    inference(negated_conjecture,[],[f10])).
% 0.21/0.44  fof(f10,conjecture,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f27,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.44    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.44  fof(f724,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.21/0.44    inference(superposition,[],[f722,f30])).
% 0.21/0.44  fof(f722,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(resolution,[],[f719,f29])).
% 0.21/0.44  fof(f719,plain,(
% 0.21/0.44    r1_tarski(k4_xboole_0(k1_xboole_0,sK0),k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(resolution,[],[f654,f78])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f75])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(superposition,[],[f55,f72])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(k1_xboole_0,X0) | r1_tarski(X0,X0)) )),
% 0.21/0.44    inference(superposition,[],[f28,f51])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 0.21/0.44    inference(superposition,[],[f25,f33])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.44  fof(f654,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK1),X0) | r1_tarski(k4_xboole_0(k1_xboole_0,sK0),X0)) )),
% 0.21/0.44    inference(forward_demodulation,[],[f649,f344])).
% 0.21/0.44  fof(f344,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(X0,sK1))) )),
% 0.21/0.44    inference(superposition,[],[f227,f23])).
% 0.21/0.44  fof(f227,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0))) )),
% 0.21/0.44    inference(superposition,[],[f30,f216])).
% 0.21/0.44  fof(f216,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.44    inference(superposition,[],[f150,f117])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 0.21/0.44    inference(superposition,[],[f30,f81])).
% 0.21/0.44  fof(f81,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(resolution,[],[f78,f29])).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK0,sK1)))) )),
% 0.21/0.44    inference(superposition,[],[f116,f23])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    ( ! [X16] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),X16)) = k4_xboole_0(k1_xboole_0,X16)) )),
% 0.21/0.44    inference(superposition,[],[f30,f62])).
% 0.21/0.44  fof(f649,plain,(
% 0.21/0.44    ( ! [X0] : (r1_tarski(k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)),X0) | ~r1_tarski(k4_xboole_0(sK0,sK1),X0)) )),
% 0.21/0.44    inference(backward_demodulation,[],[f198,f624])).
% 0.21/0.44  fof(f624,plain,(
% 0.21/0.44    ( ! [X8,X9] : (k4_xboole_0(k1_xboole_0,k2_xboole_0(X8,X9)) = k4_xboole_0(X8,k2_xboole_0(X8,X9))) )),
% 0.21/0.44    inference(superposition,[],[f124,f33])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(X2,k2_xboole_0(X3,X4))) )),
% 0.21/0.44    inference(forward_demodulation,[],[f110,f30])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    ( ! [X4,X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X3,X4)) = k4_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 0.21/0.44    inference(superposition,[],[f30,f25])).
% 0.21/0.44  fof(f198,plain,(
% 0.21/0.44    ( ! [X0] : (~r1_tarski(k4_xboole_0(sK0,sK1),X0) | r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),X0)) )),
% 0.21/0.44    inference(superposition,[],[f42,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)))),
% 0.21/0.44    inference(forward_demodulation,[],[f68,f23])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 0.21/0.44    inference(forward_demodulation,[],[f65,f30])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))),
% 0.21/0.44    inference(resolution,[],[f64,f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X4,X2,X3] : (~r1_tarski(k2_xboole_0(X3,X2),X4) | r1_tarski(X2,X4)) )),
% 0.21/0.44    inference(superposition,[],[f31,f23])).
% 0.21/0.44  fof(f1111,plain,(
% 0.21/0.44    ~spl2_3),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f1110])).
% 0.21/0.44  fof(f1110,plain,(
% 0.21/0.44    $false | ~spl2_3),
% 0.21/0.44    inference(subsumption_resolution,[],[f1109,f52])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    sK0 != k4_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(superposition,[],[f21,f25])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    sK0 != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f1109,plain,(
% 0.21/0.44    sK0 = k4_xboole_0(sK0,sK1) | ~spl2_3),
% 0.21/0.44    inference(forward_demodulation,[],[f1071,f22])).
% 0.21/0.44  fof(f1071,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) | ~spl2_3),
% 0.21/0.44    inference(backward_demodulation,[],[f657,f1067])).
% 0.21/0.44  fof(f1067,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK0) | ~spl2_3),
% 0.21/0.44    inference(backward_demodulation,[],[f656,f1066])).
% 0.21/0.44  fof(f1066,plain,(
% 0.21/0.44    k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK0) | ~spl2_3),
% 0.21/0.44    inference(resolution,[],[f777,f29])).
% 0.21/0.44  fof(f777,plain,(
% 0.21/0.44    r1_tarski(k4_xboole_0(k1_xboole_0,sK0),sK0) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f775])).
% 0.21/0.44  fof(f775,plain,(
% 0.21/0.44    spl2_3 <=> r1_tarski(k4_xboole_0(k1_xboole_0,sK0),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f656,plain,(
% 0.21/0.44    k4_xboole_0(k1_xboole_0,sK0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,sK0),sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f651,f344])).
% 0.21/0.44  fof(f651,plain,(
% 0.21/0.44    k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(backward_demodulation,[],[f201,f624])).
% 0.21/0.44  fof(f201,plain,(
% 0.21/0.44    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f200,f23])).
% 0.21/0.44  fof(f200,plain,(
% 0.21/0.44    k4_xboole_0(sK0,k2_xboole_0(sK1,sK0)) = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(forward_demodulation,[],[f196,f30])).
% 0.21/0.44  fof(f196,plain,(
% 0.21/0.44    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)),sK0)),
% 0.21/0.44    inference(superposition,[],[f49,f69])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 0.21/0.44    inference(superposition,[],[f25,f23])).
% 0.21/0.44  fof(f657,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK0))),
% 0.21/0.44    inference(forward_demodulation,[],[f652,f344])).
% 0.21/0.44  fof(f652,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k4_xboole_0(k1_xboole_0,k2_xboole_0(sK0,sK1)))),
% 0.21/0.44    inference(backward_demodulation,[],[f69,f624])).
% 0.21/0.44  fof(f782,plain,(
% 0.21/0.44    spl2_3 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f678,f779,f775])).
% 0.21/0.44  fof(f678,plain,(
% 0.21/0.44    k1_xboole_0 != k4_xboole_0(k1_xboole_0,sK0) | r1_tarski(k4_xboole_0(k1_xboole_0,sK0),sK0)),
% 0.21/0.44    inference(superposition,[],[f28,f656])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (2415)------------------------------
% 0.21/0.44  % (2415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (2415)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (2415)Memory used [KB]: 11385
% 0.21/0.44  % (2415)Time elapsed: 0.035 s
% 0.21/0.44  % (2415)------------------------------
% 0.21/0.44  % (2415)------------------------------
% 0.21/0.44  % (2405)Success in time 0.09 s
%------------------------------------------------------------------------------
