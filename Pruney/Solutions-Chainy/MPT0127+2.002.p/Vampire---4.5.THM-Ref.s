%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 328 expanded)
%              Number of leaves         :   17 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :   83 ( 341 expanded)
%              Number of equality atoms :   67 ( 324 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f574,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f537])).

fof(f537,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f536])).

fof(f536,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f535])).

fof(f535,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))
    | spl3_1 ),
    inference(backward_demodulation,[],[f219,f534])).

fof(f534,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0)) ),
    inference(backward_demodulation,[],[f46,f529])).

fof(f529,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X2,X1),X0) ),
    inference(forward_demodulation,[],[f504,f215])).

fof(f215,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k4_xboole_0(X3,X4),X5) ),
    inference(forward_demodulation,[],[f214,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f214,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X3)),X4),X5) ),
    inference(forward_demodulation,[],[f213,f118])).

fof(f118,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f55,f116])).

fof(f116,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f105,f24])).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f55,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f35,f23])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f213,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X3,k4_xboole_0(X3,X3)))),X4),X5) ),
    inference(forward_demodulation,[],[f212,f149])).

fof(f149,plain,(
    ! [X10,X11,X9] : k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(X10,X11),X9)))) = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,k5_xboole_0(X9,k4_xboole_0(X10,X9)))),X11) ),
    inference(superposition,[],[f47,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X2) ),
    inference(backward_demodulation,[],[f44,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2) ),
    inference(definition_unfolding,[],[f34,f38,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f212,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),X3)))),X5) ),
    inference(forward_demodulation,[],[f211,f35])).

fof(f211,plain,(
    ! [X4,X5,X3] : k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X4)),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),X3))),X5) ),
    inference(forward_demodulation,[],[f188,f70])).

fof(f70,plain,(
    ! [X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k5_xboole_0(k5_xboole_0(X5,X4),k5_xboole_0(X5,k4_xboole_0(X4,X5))) ),
    inference(superposition,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f38,f38])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f188,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))))),X5) = k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) ),
    inference(superposition,[],[f45,f47])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f36,f29,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f504,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f215,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f37,f29,f29])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f219,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1))))
    | spl3_1 ),
    inference(backward_demodulation,[],[f137,f215])).

fof(f137,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))
    | spl3_1 ),
    inference(superposition,[],[f103,f35])).

fof(f103,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_1
  <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f104,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f22,f40,f29,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f33,f29,f39])).

fof(f33,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f22,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (32401)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.44  % (32402)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.45  % (32394)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (32391)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (32403)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (32390)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (32395)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (32398)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (32406)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (32393)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (32396)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (32399)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (32392)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (32397)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (32400)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.51  % (32400)Refutation not found, incomplete strategy% (32400)------------------------------
% 0.20/0.51  % (32400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32400)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (32400)Memory used [KB]: 10618
% 0.20/0.51  % (32400)Time elapsed: 0.101 s
% 0.20/0.51  % (32400)------------------------------
% 0.20/0.51  % (32400)------------------------------
% 0.20/0.51  % (32404)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (32389)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.52  % (32405)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.54  % (32404)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f574,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f104,f537])).
% 0.20/0.54  fof(f537,plain,(
% 0.20/0.54    spl3_1),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f536])).
% 0.20/0.54  fof(f536,plain,(
% 0.20/0.54    $false | spl3_1),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f535])).
% 0.20/0.54  fof(f535,plain,(
% 0.20/0.54    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) | spl3_1),
% 0.20/0.54    inference(backward_demodulation,[],[f219,f534])).
% 0.20/0.54  fof(f534,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),X0))) )),
% 0.20/0.54    inference(backward_demodulation,[],[f46,f529])).
% 0.20/0.54  fof(f529,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X2,X1),X0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f504,f215])).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f214,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.20/0.54    inference(definition_unfolding,[],[f25,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.54  fof(f214,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X3)),X4),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f213,f118])).
% 0.20/0.54  fof(f118,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.54    inference(backward_demodulation,[],[f55,f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.54    inference(forward_demodulation,[],[f105,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(superposition,[],[f55,f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(superposition,[],[f35,f23])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.54  fof(f213,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(X3,k5_xboole_0(X3,k4_xboole_0(X3,X3)))),X4),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f212,f149])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X10,X11,X9] : (k5_xboole_0(X9,k5_xboole_0(k4_xboole_0(X10,X11),k5_xboole_0(X9,k4_xboole_0(k4_xboole_0(X10,X11),X9)))) = k4_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,k5_xboole_0(X9,k4_xboole_0(X10,X9)))),X11)) )),
% 0.20/0.54    inference(superposition,[],[f47,f35])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X1,X0)))),X2)) )),
% 0.20/0.54    inference(backward_demodulation,[],[f44,f35])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X2)),k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X0))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X2)) )),
% 0.20/0.54    inference(definition_unfolding,[],[f34,f38,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f30,f29])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),X3)))),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f211,f35])).
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4))) = k4_xboole_0(k5_xboole_0(k5_xboole_0(X3,k4_xboole_0(X3,X4)),k5_xboole_0(X3,k4_xboole_0(k4_xboole_0(X3,X4),X3))),X5)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f188,f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) = k5_xboole_0(k5_xboole_0(X5,X4),k5_xboole_0(X5,k4_xboole_0(X4,X5)))) )),
% 0.20/0.54    inference(superposition,[],[f43,f35])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X1,X0),k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f27,f38,f38])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.54  fof(f188,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X3,k5_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(X3,k4_xboole_0(X3,X4))))),X5) = k4_xboole_0(X3,k5_xboole_0(X4,k4_xboole_0(X5,X4)))) )),
% 0.20/0.54    inference(superposition,[],[f45,f47])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f36,f29,f38])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.20/0.54  fof(f504,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X2,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X2,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.20/0.54    inference(superposition,[],[f215,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f26,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X2) = k5_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X0,X2)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f37,f29,f29])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.20/0.54  fof(f219,plain,(
% 0.20/0.54    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k4_xboole_0(k1_tarski(sK2),k1_tarski(sK0)),k1_tarski(sK1)))) | spl3_1),
% 0.20/0.54    inference(backward_demodulation,[],[f137,f215])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))) | spl3_1),
% 0.20/0.54    inference(superposition,[],[f103,f35])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) | spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f101])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    spl3_1 <=> k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    ~spl3_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f41,f101])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),
% 0.20/0.54    inference(definition_unfolding,[],[f22,f40,f29,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f28,f29])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.20/0.54    inference(definition_unfolding,[],[f33,f29,f39])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f14])).
% 0.20/0.54  fof(f14,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.54    inference(negated_conjecture,[],[f15])).
% 0.20/0.54  fof(f15,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (32404)------------------------------
% 0.20/0.54  % (32404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32404)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (32404)Memory used [KB]: 11129
% 0.20/0.54  % (32404)Time elapsed: 0.142 s
% 0.20/0.54  % (32404)------------------------------
% 0.20/0.54  % (32404)------------------------------
% 0.20/0.55  % (32384)Success in time 0.19 s
%------------------------------------------------------------------------------
