%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:15 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 264 expanded)
%              Number of leaves         :   18 (  84 expanded)
%              Depth                    :   17
%              Number of atoms          :  129 ( 332 expanded)
%              Number of equality atoms :   81 ( 237 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2094,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f2080,f2093])).

fof(f2093,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2092])).

fof(f2092,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f2091,f1432])).

fof(f1432,plain,(
    ! [X12,X13] : k4_xboole_0(X12,X12) = k4_xboole_0(X13,X13) ),
    inference(superposition,[],[f388,f327])).

fof(f327,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1 ),
    inference(unit_resulting_resolution,[],[f307,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f307,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f62,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f388,plain,(
    ! [X4,X5] : k2_xboole_0(X5,k4_xboole_0(X4,X4)) = X5 ),
    inference(superposition,[],[f327,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2091,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2090,f203])).

fof(f203,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f71,f65])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2090,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2089,f65])).

fof(f2089,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2088,f1769])).

fof(f1769,plain,(
    ! [X23,X21,X22] : k4_xboole_0(k2_xboole_0(X21,X22),k4_xboole_0(X23,k4_xboole_0(X23,X22))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X21,X22),X23),k4_xboole_0(X21,X22)) ),
    inference(superposition,[],[f102,f71])).

fof(f102,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f79,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f79,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f2088,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f2087,f930])).

fof(f930,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f98,f97])).

fof(f97,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f68,f67])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f2087,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2086,f205])).

fof(f205,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f2086,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2085,f478])).

fof(f478,plain,(
    ! [X14,X15,X16] : k2_xboole_0(X14,k2_xboole_0(k4_xboole_0(X14,X15),X16)) = k2_xboole_0(X14,X16) ),
    inference(superposition,[],[f78,f132])).

fof(f132,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f126,f65])).

fof(f126,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unit_resulting_resolution,[],[f63,f74])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f78,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f2085,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2084,f515])).

fof(f515,plain,(
    ! [X14,X15,X16] : k2_xboole_0(X14,k2_xboole_0(X15,X16)) = k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,X14))) ),
    inference(forward_demodulation,[],[f514,f78])).

fof(f514,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,X14))) ),
    inference(forward_demodulation,[],[f486,f421])).

fof(f421,plain,(
    ! [X12,X13,X11] : k2_xboole_0(X13,k4_xboole_0(X11,X12)) = k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f70,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f486,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X14,X15)))) ),
    inference(superposition,[],[f78,f70])).

fof(f2084,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2083,f483])).

% (3555)Time limit reached!
% (3555)------------------------------
% (3555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3555)Termination reason: Time limit
fof(f483,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f78,f65])).

% (3555)Termination phase: Saturation

% (3555)Memory used [KB]: 10874
% (3555)Time elapsed: 0.600 s
fof(f2083,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2082,f515])).

% (3555)------------------------------
% (3555)------------------------------
fof(f2082,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2081,f483])).

fof(f2081,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2066,f77])).

fof(f2066,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f113,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f113,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_1
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2080,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f2079])).

fof(f2079,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f2078,f1432])).

fof(f2078,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2077,f203])).

fof(f2077,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2076,f65])).

fof(f2076,plain,
    ( k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2075,f1769])).

fof(f2075,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,sK0)
    | spl3_1 ),
    inference(forward_demodulation,[],[f2074,f930])).

fof(f2074,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2073,f205])).

fof(f2073,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2072,f478])).

fof(f2072,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2071,f515])).

fof(f2071,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2070,f483])).

fof(f2070,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2069,f515])).

fof(f2069,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2068,f483])).

fof(f2068,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f2067,f77])).

fof(f2067,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f113,f75])).

fof(f114,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f94,f111])).

fof(f94,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f59,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f55])).

fof(f55,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (3566)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (3557)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (3558)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (3550)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (3565)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (3550)Refutation not found, incomplete strategy% (3550)------------------------------
% 0.21/0.52  % (3550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3550)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3550)Memory used [KB]: 10746
% 0.21/0.52  % (3550)Time elapsed: 0.099 s
% 0.21/0.52  % (3550)------------------------------
% 0.21/0.52  % (3550)------------------------------
% 0.21/0.52  % (3565)Refutation not found, incomplete strategy% (3565)------------------------------
% 0.21/0.52  % (3565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3573)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.53  % (3549)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.53  % (3565)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (3565)Memory used [KB]: 10618
% 1.24/0.53  % (3565)Time elapsed: 0.104 s
% 1.24/0.53  % (3565)------------------------------
% 1.24/0.53  % (3565)------------------------------
% 1.24/0.53  % (3569)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.24/0.53  % (3569)Refutation not found, incomplete strategy% (3569)------------------------------
% 1.24/0.53  % (3569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (3569)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (3569)Memory used [KB]: 1791
% 1.24/0.53  % (3569)Time elapsed: 0.095 s
% 1.24/0.53  % (3569)------------------------------
% 1.24/0.53  % (3569)------------------------------
% 1.24/0.53  % (3554)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.53  % (3551)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (3571)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.54  % (3548)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (3548)Refutation not found, incomplete strategy% (3548)------------------------------
% 1.24/0.54  % (3548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (3548)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (3548)Memory used [KB]: 1663
% 1.24/0.54  % (3548)Time elapsed: 0.123 s
% 1.24/0.54  % (3548)------------------------------
% 1.24/0.54  % (3548)------------------------------
% 1.24/0.54  % (3572)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.54  % (3563)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.54  % (3564)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.54  % (3561)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.54  % (3575)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.55  % (3555)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.55  % (3560)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.49/0.55  % (3576)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.49/0.55  % (3556)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.55  % (3567)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.49/0.55  % (3562)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.55  % (3552)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.55  % (3559)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (3553)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.49/0.56  % (3568)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.56  % (3570)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.56  % (3568)Refutation not found, incomplete strategy% (3568)------------------------------
% 1.49/0.56  % (3568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (3568)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (3568)Memory used [KB]: 10746
% 1.49/0.56  % (3568)Time elapsed: 0.147 s
% 1.49/0.56  % (3568)------------------------------
% 1.49/0.56  % (3568)------------------------------
% 1.49/0.57  % (3577)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.49/0.57  % (3556)Refutation not found, incomplete strategy% (3556)------------------------------
% 1.49/0.57  % (3556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (3556)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (3556)Memory used [KB]: 10618
% 1.49/0.57  % (3556)Time elapsed: 0.156 s
% 1.49/0.57  % (3556)------------------------------
% 1.49/0.57  % (3556)------------------------------
% 1.49/0.57  % (3574)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.08/0.66  % (3579)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.08/0.66  % (3578)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.08/0.67  % (3580)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.08/0.68  % (3581)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.42/0.70  % (3583)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.42/0.74  % (3582)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.36/0.86  % (3553)Time limit reached!
% 3.36/0.86  % (3553)------------------------------
% 3.36/0.86  % (3553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.86  % (3553)Termination reason: Time limit
% 3.36/0.86  
% 3.36/0.86  % (3553)Memory used [KB]: 8571
% 3.36/0.86  % (3553)Time elapsed: 0.422 s
% 3.36/0.86  % (3553)------------------------------
% 3.36/0.86  % (3553)------------------------------
% 3.68/0.90  % (3560)Time limit reached!
% 3.68/0.90  % (3560)------------------------------
% 3.68/0.90  % (3560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.90  % (3560)Termination reason: Time limit
% 3.68/0.90  % (3560)Termination phase: Saturation
% 3.68/0.90  
% 3.68/0.90  % (3560)Memory used [KB]: 8571
% 3.68/0.90  % (3560)Time elapsed: 0.500 s
% 3.68/0.90  % (3560)------------------------------
% 3.68/0.90  % (3560)------------------------------
% 3.68/0.93  % (3549)Time limit reached!
% 3.68/0.93  % (3549)------------------------------
% 3.68/0.93  % (3549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.93  % (3549)Termination reason: Time limit
% 3.68/0.93  
% 3.68/0.93  % (3549)Memory used [KB]: 7931
% 3.68/0.93  % (3549)Time elapsed: 0.513 s
% 3.68/0.93  % (3549)------------------------------
% 3.68/0.93  % (3549)------------------------------
% 3.68/0.93  % (3558)Time limit reached!
% 3.68/0.93  % (3558)------------------------------
% 3.68/0.93  % (3558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.93  % (3558)Termination reason: Time limit
% 3.68/0.93  % (3558)Termination phase: Saturation
% 3.68/0.93  
% 3.68/0.93  % (3558)Memory used [KB]: 13944
% 3.68/0.93  % (3558)Time elapsed: 0.500 s
% 3.68/0.93  % (3558)------------------------------
% 3.68/0.93  % (3558)------------------------------
% 3.97/0.96  % (3584)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 3.97/0.99  % (3581)Time limit reached!
% 3.97/0.99  % (3581)------------------------------
% 3.97/0.99  % (3581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/0.99  % (3581)Termination reason: Time limit
% 3.97/0.99  
% 3.97/0.99  % (3581)Memory used [KB]: 7803
% 3.97/0.99  % (3581)Time elapsed: 0.419 s
% 3.97/0.99  % (3581)------------------------------
% 3.97/0.99  % (3581)------------------------------
% 3.97/1.01  % (3583)Refutation found. Thanks to Tanya!
% 3.97/1.01  % SZS status Theorem for theBenchmark
% 3.97/1.01  % SZS output start Proof for theBenchmark
% 3.97/1.01  fof(f2094,plain,(
% 3.97/1.01    $false),
% 3.97/1.01    inference(avatar_sat_refutation,[],[f114,f2080,f2093])).
% 3.97/1.01  fof(f2093,plain,(
% 3.97/1.01    spl3_1),
% 3.97/1.01    inference(avatar_contradiction_clause,[],[f2092])).
% 3.97/1.01  fof(f2092,plain,(
% 3.97/1.01    $false | spl3_1),
% 3.97/1.01    inference(subsumption_resolution,[],[f2091,f1432])).
% 3.97/1.01  fof(f1432,plain,(
% 3.97/1.01    ( ! [X12,X13] : (k4_xboole_0(X12,X12) = k4_xboole_0(X13,X13)) )),
% 3.97/1.01    inference(superposition,[],[f388,f327])).
% 3.97/1.01  fof(f327,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X0),X1) = X1) )),
% 3.97/1.01    inference(unit_resulting_resolution,[],[f307,f74])).
% 3.97/1.01  fof(f74,plain,(
% 3.97/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.97/1.01    inference(cnf_transformation,[],[f39])).
% 3.97/1.01  fof(f39,plain,(
% 3.97/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.97/1.01    inference(ennf_transformation,[],[f7])).
% 3.97/1.01  fof(f7,axiom,(
% 3.97/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.97/1.01  fof(f307,plain,(
% 3.97/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 3.97/1.01    inference(unit_resulting_resolution,[],[f62,f85])).
% 3.97/1.01  fof(f85,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f44])).
% 3.97/1.01  fof(f44,plain,(
% 3.97/1.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.97/1.01    inference(ennf_transformation,[],[f20])).
% 3.97/1.01  fof(f20,axiom,(
% 3.97/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.97/1.01  fof(f62,plain,(
% 3.97/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f30])).
% 3.97/1.01  fof(f30,axiom,(
% 3.97/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.97/1.01  fof(f388,plain,(
% 3.97/1.01    ( ! [X4,X5] : (k2_xboole_0(X5,k4_xboole_0(X4,X4)) = X5) )),
% 3.97/1.01    inference(superposition,[],[f327,f65])).
% 3.97/1.01  fof(f65,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f1])).
% 3.97/1.01  fof(f1,axiom,(
% 3.97/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.97/1.01  fof(f2091,plain,(
% 3.97/1.01    k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2090,f203])).
% 3.97/1.01  fof(f203,plain,(
% 3.97/1.01    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 3.97/1.01    inference(superposition,[],[f71,f65])).
% 3.97/1.01  fof(f71,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f18])).
% 3.97/1.01  fof(f18,axiom,(
% 3.97/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.97/1.01  fof(f2090,plain,(
% 3.97/1.01    k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK0))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2089,f65])).
% 3.97/1.01  fof(f2089,plain,(
% 3.97/1.01    k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2088,f1769])).
% 3.97/1.01  fof(f1769,plain,(
% 3.97/1.01    ( ! [X23,X21,X22] : (k4_xboole_0(k2_xboole_0(X21,X22),k4_xboole_0(X23,k4_xboole_0(X23,X22))) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X21,X22),X23),k4_xboole_0(X21,X22))) )),
% 3.97/1.01    inference(superposition,[],[f102,f71])).
% 3.97/1.01  fof(f102,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 3.97/1.01    inference(definition_unfolding,[],[f79,f67])).
% 3.97/1.01  fof(f67,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f23])).
% 3.97/1.01  fof(f23,axiom,(
% 3.97/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.97/1.01  fof(f79,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f28])).
% 3.97/1.01  fof(f28,axiom,(
% 3.97/1.01    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_xboole_1)).
% 3.97/1.01  fof(f2088,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,sK0) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2087,f930])).
% 3.97/1.01  fof(f930,plain,(
% 3.97/1.01    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)) )),
% 3.97/1.01    inference(superposition,[],[f98,f97])).
% 3.97/1.01  fof(f97,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 3.97/1.01    inference(definition_unfolding,[],[f66,f67])).
% 3.97/1.01  fof(f66,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.97/1.01    inference(cnf_transformation,[],[f11])).
% 3.97/1.01  fof(f11,axiom,(
% 3.97/1.01    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 3.97/1.01  fof(f98,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.97/1.01    inference(definition_unfolding,[],[f68,f67])).
% 3.97/1.01  fof(f68,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f22])).
% 3.97/1.01  fof(f22,axiom,(
% 3.97/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.97/1.01  fof(f2087,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2086,f205])).
% 3.97/1.01  fof(f205,plain,(
% 3.97/1.01    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 3.97/1.01    inference(superposition,[],[f71,f69])).
% 3.97/1.01  fof(f69,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f29])).
% 3.97/1.01  fof(f29,axiom,(
% 3.97/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 3.97/1.01  fof(f2086,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2085,f478])).
% 3.97/1.01  fof(f478,plain,(
% 3.97/1.01    ( ! [X14,X15,X16] : (k2_xboole_0(X14,k2_xboole_0(k4_xboole_0(X14,X15),X16)) = k2_xboole_0(X14,X16)) )),
% 3.97/1.01    inference(superposition,[],[f78,f132])).
% 3.97/1.01  fof(f132,plain,(
% 3.97/1.01    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 3.97/1.01    inference(superposition,[],[f126,f65])).
% 3.97/1.01  fof(f126,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 3.97/1.01    inference(unit_resulting_resolution,[],[f63,f74])).
% 3.97/1.01  fof(f63,plain,(
% 3.97/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.97/1.01    inference(cnf_transformation,[],[f16])).
% 3.97/1.01  fof(f16,axiom,(
% 3.97/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.97/1.01  fof(f78,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f24])).
% 3.97/1.01  fof(f24,axiom,(
% 3.97/1.01    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 3.97/1.01  fof(f2085,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2084,f515])).
% 3.97/1.01  fof(f515,plain,(
% 3.97/1.01    ( ! [X14,X15,X16] : (k2_xboole_0(X14,k2_xboole_0(X15,X16)) = k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,X14)))) )),
% 3.97/1.01    inference(forward_demodulation,[],[f514,f78])).
% 3.97/1.01  fof(f514,plain,(
% 3.97/1.01    ( ! [X14,X15,X16] : (k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,X14)))) )),
% 3.97/1.01    inference(forward_demodulation,[],[f486,f421])).
% 3.97/1.01  fof(f421,plain,(
% 3.97/1.01    ( ! [X12,X13,X11] : (k2_xboole_0(X13,k4_xboole_0(X11,X12)) = k2_xboole_0(X13,k4_xboole_0(X11,k2_xboole_0(X12,X13)))) )),
% 3.97/1.01    inference(superposition,[],[f70,f77])).
% 3.97/1.01  fof(f77,plain,(
% 3.97/1.01    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f19])).
% 3.97/1.01  fof(f19,axiom,(
% 3.97/1.01    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.97/1.01  fof(f70,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.97/1.01    inference(cnf_transformation,[],[f17])).
% 3.97/1.01  fof(f17,axiom,(
% 3.97/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.97/1.01  fof(f486,plain,(
% 3.97/1.01    ( ! [X14,X15,X16] : (k2_xboole_0(k2_xboole_0(X14,X15),X16) = k2_xboole_0(X14,k2_xboole_0(X15,k4_xboole_0(X16,k2_xboole_0(X14,X15))))) )),
% 3.97/1.01    inference(superposition,[],[f78,f70])).
% 3.97/1.01  fof(f2084,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2083,f483])).
% 3.97/1.01  % (3555)Time limit reached!
% 3.97/1.01  % (3555)------------------------------
% 3.97/1.01  % (3555)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.01  % (3555)Termination reason: Time limit
% 3.97/1.01  fof(f483,plain,(
% 3.97/1.01    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k2_xboole_0(X5,X6)) = k2_xboole_0(X5,k2_xboole_0(X6,X7))) )),
% 3.97/1.01    inference(superposition,[],[f78,f65])).
% 3.97/1.01  % (3555)Termination phase: Saturation
% 3.97/1.01  
% 3.97/1.01  % (3555)Memory used [KB]: 10874
% 3.97/1.01  % (3555)Time elapsed: 0.600 s
% 3.97/1.01  fof(f2083,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2082,f515])).
% 3.97/1.01  % (3555)------------------------------
% 3.97/1.01  % (3555)------------------------------
% 3.97/1.01  fof(f2082,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2081,f483])).
% 3.97/1.01  fof(f2081,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2066,f77])).
% 3.97/1.01  fof(f2066,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl3_1),
% 3.97/1.01    inference(unit_resulting_resolution,[],[f113,f75])).
% 3.97/1.01  fof(f75,plain,(
% 3.97/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 3.97/1.01    inference(cnf_transformation,[],[f40])).
% 3.97/1.01  fof(f40,plain,(
% 3.97/1.01    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f14])).
% 3.97/1.01  fof(f14,axiom,(
% 3.97/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 3.97/1.01  fof(f113,plain,(
% 3.97/1.01    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl3_1),
% 3.97/1.01    inference(avatar_component_clause,[],[f111])).
% 3.97/1.01  fof(f111,plain,(
% 3.97/1.01    spl3_1 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.97/1.01    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.97/1.01  fof(f2080,plain,(
% 3.97/1.01    spl3_1),
% 3.97/1.01    inference(avatar_contradiction_clause,[],[f2079])).
% 3.97/1.01  fof(f2079,plain,(
% 3.97/1.01    $false | spl3_1),
% 3.97/1.01    inference(subsumption_resolution,[],[f2078,f1432])).
% 3.97/1.01  fof(f2078,plain,(
% 3.97/1.01    k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2077,f203])).
% 3.97/1.01  fof(f2077,plain,(
% 3.97/1.01    k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),sK0))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2076,f65])).
% 3.97/1.01  fof(f2076,plain,(
% 3.97/1.01    k4_xboole_0(sK0,sK0) != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),sK0),k4_xboole_0(sK0,sK1))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2075,f1769])).
% 3.97/1.01  fof(f2075,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,sK0) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2074,f930])).
% 3.97/1.01  fof(f2074,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2073,f205])).
% 3.97/1.01  fof(f2073,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2072,f478])).
% 3.97/1.01  fof(f2072,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2071,f515])).
% 3.97/1.01  fof(f2071,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2070,f483])).
% 3.97/1.01  fof(f2070,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2069,f515])).
% 3.97/1.01  fof(f2069,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2068,f483])).
% 3.97/1.01  fof(f2068,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) | spl3_1),
% 3.97/1.01    inference(forward_demodulation,[],[f2067,f77])).
% 3.97/1.01  fof(f2067,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | spl3_1),
% 3.97/1.01    inference(unit_resulting_resolution,[],[f113,f75])).
% 3.97/1.01  fof(f114,plain,(
% 3.97/1.01    ~spl3_1),
% 3.97/1.01    inference(avatar_split_clause,[],[f94,f111])).
% 3.97/1.01  fof(f94,plain,(
% 3.97/1.01    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.97/1.01    inference(definition_unfolding,[],[f59,f67])).
% 3.97/1.01  fof(f59,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.97/1.01    inference(cnf_transformation,[],[f56])).
% 3.97/1.01  fof(f56,plain,(
% 3.97/1.01    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.97/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f55])).
% 3.97/1.01  fof(f55,plain,(
% 3.97/1.01    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 3.97/1.01    introduced(choice_axiom,[])).
% 3.97/1.01  fof(f37,plain,(
% 3.97/1.01    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.97/1.01    inference(ennf_transformation,[],[f34])).
% 3.97/1.01  fof(f34,negated_conjecture,(
% 3.97/1.01    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.97/1.01    inference(negated_conjecture,[],[f33])).
% 3.97/1.01  fof(f33,conjecture,(
% 3.97/1.01    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 3.97/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 3.97/1.01  % SZS output end Proof for theBenchmark
% 3.97/1.01  % (3583)------------------------------
% 3.97/1.01  % (3583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.97/1.01  % (3583)Termination reason: Refutation
% 3.97/1.01  
% 3.97/1.01  % (3583)Memory used [KB]: 2942
% 3.97/1.01  % (3583)Time elapsed: 0.367 s
% 3.97/1.01  % (3583)------------------------------
% 3.97/1.01  % (3583)------------------------------
% 3.97/1.01  % (3547)Success in time 0.644 s
%------------------------------------------------------------------------------
