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
% DateTime   : Thu Dec  3 12:40:18 EST 2020

% Result     : Theorem 52.72s
% Output     : Refutation 52.72s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 688 expanded)
%              Number of leaves         :   24 ( 243 expanded)
%              Depth                    :   16
%              Number of atoms          :  134 ( 743 expanded)
%              Number of equality atoms :   76 ( 668 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11368,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f81,f86,f93,f222,f11365])).

fof(f11365,plain,
    ( ~ spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f11364])).

fof(f11364,plain,
    ( $false
    | ~ spl2_2
    | spl2_5 ),
    inference(subsumption_resolution,[],[f11363,f95])).

fof(f95,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f80,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(X1,k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))) ) ),
    inference(backward_demodulation,[],[f56,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f51,f49,f51])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f47])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f80,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f11363,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_5 ),
    inference(forward_demodulation,[],[f11362,f197])).

fof(f197,plain,(
    ! [X6,X4,X7,X5] : k5_enumset1(X7,X7,X7,X7,X6,X5,X4) = k5_enumset1(X4,X5,X6,X7,X7,X7,X7) ),
    inference(superposition,[],[f107,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f36,f45,f45])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f107,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X1,X2,X3,X3,X3,X3) ),
    inference(superposition,[],[f58,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f40,f48,f46,f45])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f41,f48,f39,f51])).

fof(f41,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f11362,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1))))
    | spl2_5 ),
    inference(forward_demodulation,[],[f11352,f9559])).

fof(f9559,plain,(
    ! [X17,X18,X16] : k5_enumset1(X18,X18,X18,X18,X17,X17,X16) = k5_enumset1(X17,X16,X16,X18,X18,X18,X18) ),
    inference(superposition,[],[f232,f197])).

fof(f232,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X0,X0,X2,X3,X4,X5) ),
    inference(superposition,[],[f97,f52])).

fof(f97,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X3,X3,X3,X3,X4,X5,X6))) ),
    inference(superposition,[],[f52,f57])).

fof(f11352,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))))
    | spl2_5 ),
    inference(superposition,[],[f221,f454])).

fof(f454,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X5,X4,X3,X3) ),
    inference(superposition,[],[f115,f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k3_tarski(k5_enumset1(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X3,X3,X3,X3,X2,X1,X0))) ),
    inference(superposition,[],[f52,f57])).

fof(f115,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6))) ),
    inference(superposition,[],[f59,f52])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f43,f50,f48,f39,f46])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X6,X7,X8))) ),
    inference(definition_unfolding,[],[f42,f48,f44,f45])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).

fof(f221,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl2_5
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f222,plain,
    ( ~ spl2_5
    | spl2_4 ),
    inference(avatar_split_clause,[],[f94,f90,f219])).

fof(f90,plain,
    ( spl2_4
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f94,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))
    | spl2_4 ),
    inference(superposition,[],[f92,f35])).

fof(f92,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f93,plain,
    ( ~ spl2_4
    | spl2_3 ),
    inference(avatar_split_clause,[],[f88,f83,f90])).

fof(f83,plain,
    ( spl2_3
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f88,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_3 ),
    inference(forward_demodulation,[],[f87,f28])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f87,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | spl2_3 ),
    inference(forward_demodulation,[],[f85,f57])).

fof(f85,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f86,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f53,f83])).

fof(f53,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f26,f51,f49,f51])).

fof(f26,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f81,plain,
    ( spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f75,f62,f78])).

fof(f62,plain,
    ( spl2_1
  <=> r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f75,plain,
    ( r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f64,plain,
    ( ~ r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f65,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f54,f62])).

fof(f54,plain,(
    ~ r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f25,f51])).

fof(f25,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:17:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (24537)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.46  % (24546)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (24534)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (24541)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (24536)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (24547)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (24545)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (24532)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (24542)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (24542)Refutation not found, incomplete strategy% (24542)------------------------------
% 0.22/0.48  % (24542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24542)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (24542)Memory used [KB]: 10618
% 0.22/0.48  % (24542)Time elapsed: 0.072 s
% 0.22/0.48  % (24542)------------------------------
% 0.22/0.48  % (24542)------------------------------
% 0.22/0.48  % (24539)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (24543)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (24533)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (24548)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (24535)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (24544)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.50  % (24540)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (24531)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (24538)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 4.85/1.02  % (24535)Time limit reached!
% 4.85/1.02  % (24535)------------------------------
% 4.85/1.02  % (24535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.85/1.02  % (24535)Termination reason: Time limit
% 4.85/1.02  % (24535)Termination phase: Saturation
% 4.85/1.02  
% 4.85/1.02  % (24535)Memory used [KB]: 15351
% 4.85/1.02  % (24535)Time elapsed: 0.600 s
% 4.85/1.02  % (24535)------------------------------
% 4.85/1.02  % (24535)------------------------------
% 12.54/1.93  % (24536)Time limit reached!
% 12.54/1.93  % (24536)------------------------------
% 12.54/1.93  % (24536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.93  % (24536)Termination reason: Time limit
% 12.54/1.93  % (24536)Termination phase: Saturation
% 12.54/1.93  
% 12.54/1.93  % (24536)Memory used [KB]: 42856
% 12.54/1.93  % (24536)Time elapsed: 1.500 s
% 12.54/1.93  % (24536)------------------------------
% 12.54/1.93  % (24536)------------------------------
% 12.54/1.93  % (24537)Time limit reached!
% 12.54/1.93  % (24537)------------------------------
% 12.54/1.93  % (24537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.54/1.94  % (24537)Termination reason: Time limit
% 12.54/1.94  % (24537)Termination phase: Saturation
% 12.54/1.94  
% 12.54/1.94  % (24537)Memory used [KB]: 35180
% 12.54/1.94  % (24537)Time elapsed: 1.500 s
% 12.54/1.94  % (24537)------------------------------
% 12.54/1.94  % (24537)------------------------------
% 14.36/2.22  % (24533)Time limit reached!
% 14.36/2.22  % (24533)------------------------------
% 14.36/2.22  % (24533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.36/2.22  % (24533)Termination reason: Time limit
% 14.36/2.22  % (24533)Termination phase: Saturation
% 14.36/2.22  
% 14.36/2.22  % (24533)Memory used [KB]: 38123
% 14.36/2.22  % (24533)Time elapsed: 1.801 s
% 14.36/2.22  % (24533)------------------------------
% 14.36/2.22  % (24533)------------------------------
% 18.29/2.65  % (24543)Time limit reached!
% 18.29/2.65  % (24543)------------------------------
% 18.29/2.65  % (24543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.29/2.65  % (24543)Termination reason: Time limit
% 18.29/2.65  % (24543)Termination phase: Saturation
% 18.29/2.65  
% 18.29/2.65  % (24543)Memory used [KB]: 37739
% 18.29/2.65  % (24543)Time elapsed: 2.200 s
% 18.29/2.65  % (24543)------------------------------
% 18.29/2.65  % (24543)------------------------------
% 52.72/7.01  % (24546)Refutation found. Thanks to Tanya!
% 52.72/7.01  % SZS status Theorem for theBenchmark
% 52.72/7.01  % SZS output start Proof for theBenchmark
% 52.72/7.01  fof(f11368,plain,(
% 52.72/7.01    $false),
% 52.72/7.01    inference(avatar_sat_refutation,[],[f65,f81,f86,f93,f222,f11365])).
% 52.72/7.01  fof(f11365,plain,(
% 52.72/7.01    ~spl2_2 | spl2_5),
% 52.72/7.01    inference(avatar_contradiction_clause,[],[f11364])).
% 52.72/7.01  fof(f11364,plain,(
% 52.72/7.01    $false | (~spl2_2 | spl2_5)),
% 52.72/7.01    inference(subsumption_resolution,[],[f11363,f95])).
% 52.72/7.01  fof(f95,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | ~spl2_2),
% 52.72/7.01    inference(unit_resulting_resolution,[],[f80,f60])).
% 52.72/7.01  fof(f60,plain,(
% 52.72/7.01    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(X1,k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))))) )),
% 52.72/7.01    inference(backward_demodulation,[],[f56,f35])).
% 52.72/7.01  fof(f35,plain,(
% 52.72/7.01    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f2])).
% 52.72/7.01  fof(f2,axiom,(
% 52.72/7.01    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 52.72/7.01  fof(f56,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k5_xboole_0(k5_xboole_0(X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)),k3_tarski(k5_enumset1(X1,X1,X1,X1,X1,X1,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)))) | ~r2_hidden(X0,X1)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f33,f51,f49,f51])).
% 52.72/7.01  fof(f49,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 52.72/7.01    inference(definition_unfolding,[],[f31,f48])).
% 52.72/7.01  fof(f48,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 52.72/7.01    inference(definition_unfolding,[],[f29,f47])).
% 52.72/7.01  fof(f47,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f30,f46])).
% 52.72/7.01  fof(f46,plain,(
% 52.72/7.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f34,f45])).
% 52.72/7.01  fof(f45,plain,(
% 52.72/7.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f37,f44])).
% 52.72/7.01  fof(f44,plain,(
% 52.72/7.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f38,f39])).
% 52.72/7.01  fof(f39,plain,(
% 52.72/7.01    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f14])).
% 52.72/7.01  fof(f14,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 52.72/7.01  fof(f38,plain,(
% 52.72/7.01    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f13])).
% 52.72/7.01  fof(f13,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 52.72/7.01  fof(f37,plain,(
% 52.72/7.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f12])).
% 52.72/7.01  fof(f12,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 52.72/7.01  fof(f34,plain,(
% 52.72/7.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f11])).
% 52.72/7.01  fof(f11,axiom,(
% 52.72/7.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 52.72/7.01  fof(f30,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f10])).
% 52.72/7.01  fof(f10,axiom,(
% 52.72/7.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 52.72/7.01  fof(f29,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f17])).
% 52.72/7.01  fof(f17,axiom,(
% 52.72/7.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 52.72/7.01  fof(f31,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f3])).
% 52.72/7.01  fof(f3,axiom,(
% 52.72/7.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 52.72/7.01  fof(f51,plain,(
% 52.72/7.01    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f27,f47])).
% 52.72/7.01  fof(f27,plain,(
% 52.72/7.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f9])).
% 52.72/7.01  fof(f9,axiom,(
% 52.72/7.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 52.72/7.01  fof(f33,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f22])).
% 52.72/7.01  fof(f22,plain,(
% 52.72/7.01    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 52.72/7.01    inference(ennf_transformation,[],[f16])).
% 52.72/7.01  fof(f16,axiom,(
% 52.72/7.01    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 52.72/7.01  fof(f80,plain,(
% 52.72/7.01    r2_hidden(sK0,sK1) | ~spl2_2),
% 52.72/7.01    inference(avatar_component_clause,[],[f78])).
% 52.72/7.01  fof(f78,plain,(
% 52.72/7.01    spl2_2 <=> r2_hidden(sK0,sK1)),
% 52.72/7.01    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 52.72/7.01  fof(f11363,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | spl2_5),
% 52.72/7.01    inference(forward_demodulation,[],[f11362,f197])).
% 52.72/7.01  fof(f197,plain,(
% 52.72/7.01    ( ! [X6,X4,X7,X5] : (k5_enumset1(X7,X7,X7,X7,X6,X5,X4) = k5_enumset1(X4,X5,X6,X7,X7,X7,X7)) )),
% 52.72/7.01    inference(superposition,[],[f107,f57])).
% 52.72/7.01  fof(f57,plain,(
% 52.72/7.01    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X3,X3,X3,X3,X2,X1,X0)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f36,f45,f45])).
% 52.72/7.01  fof(f36,plain,(
% 52.72/7.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f4])).
% 52.72/7.01  fof(f4,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 52.72/7.01  fof(f107,plain,(
% 52.72/7.01    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k5_enumset1(X0,X1,X2,X3,X3,X3,X3)) )),
% 52.72/7.01    inference(superposition,[],[f58,f52])).
% 52.72/7.01  fof(f52,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X0,X0,X0,X0,X0,X1,X2),k5_enumset1(X3,X3,X3,X3,X4,X5,X6)))) )),
% 52.72/7.01    inference(definition_unfolding,[],[f40,f48,f46,f45])).
% 52.72/7.01  fof(f40,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f7])).
% 52.72/7.01  fof(f7,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 52.72/7.01  fof(f58,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 52.72/7.01    inference(definition_unfolding,[],[f41,f48,f39,f51])).
% 52.72/7.01  fof(f41,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f8])).
% 52.72/7.01  fof(f8,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 52.72/7.01  fof(f11362,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK1,sK1,sK1,sK1,sK1)))) | spl2_5),
% 52.72/7.01    inference(forward_demodulation,[],[f11352,f9559])).
% 52.72/7.01  fof(f9559,plain,(
% 52.72/7.01    ( ! [X17,X18,X16] : (k5_enumset1(X18,X18,X18,X18,X17,X17,X16) = k5_enumset1(X17,X16,X16,X18,X18,X18,X18)) )),
% 52.72/7.01    inference(superposition,[],[f232,f197])).
% 52.72/7.01  fof(f232,plain,(
% 52.72/7.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X1,X2,X3,X4,X5) = k5_enumset1(X1,X0,X0,X2,X3,X4,X5)) )),
% 52.72/7.01    inference(superposition,[],[f97,f52])).
% 52.72/7.01  fof(f97,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X2,X2,X2,X2,X1,X0,X0),k5_enumset1(X3,X3,X3,X3,X4,X5,X6)))) )),
% 52.72/7.01    inference(superposition,[],[f52,f57])).
% 52.72/7.01  fof(f11352,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))) | spl2_5),
% 52.72/7.01    inference(superposition,[],[f221,f454])).
% 52.72/7.01  fof(f454,plain,(
% 52.72/7.01    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X1,X2,X5,X4,X3,X3)) )),
% 52.72/7.01    inference(superposition,[],[f115,f99])).
% 52.72/7.01  fof(f99,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k3_tarski(k5_enumset1(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X3,X3,X3,X3,X2,X1,X0)))) )),
% 52.72/7.01    inference(superposition,[],[f52,f57])).
% 52.72/7.01  fof(f115,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6)))) )),
% 52.72/7.01    inference(superposition,[],[f59,f52])).
% 52.72/7.01  fof(f59,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X6,X7,X8))) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X7,X8)))) )),
% 52.72/7.01    inference(definition_unfolding,[],[f43,f50,f48,f39,f46])).
% 52.72/7.01  fof(f50,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_enumset1(X5,X5,X5,X5,X6,X7,X8)))) )),
% 52.72/7.01    inference(definition_unfolding,[],[f42,f48,f44,f45])).
% 52.72/7.01  fof(f42,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f5])).
% 52.72/7.01  fof(f5,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_enumset1(X5,X6,X7,X8))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_enumset1)).
% 52.72/7.01  fof(f43,plain,(
% 52.72/7.01    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))) )),
% 52.72/7.01    inference(cnf_transformation,[],[f6])).
% 52.72/7.01  fof(f6,axiom,(
% 52.72/7.01    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_enumset1(X6,X7,X8))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_enumset1)).
% 52.72/7.01  fof(f221,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | spl2_5),
% 52.72/7.01    inference(avatar_component_clause,[],[f219])).
% 52.72/7.01  fof(f219,plain,(
% 52.72/7.01    spl2_5 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))))),
% 52.72/7.01    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 52.72/7.01  fof(f222,plain,(
% 52.72/7.01    ~spl2_5 | spl2_4),
% 52.72/7.01    inference(avatar_split_clause,[],[f94,f90,f219])).
% 52.72/7.01  fof(f90,plain,(
% 52.72/7.01    spl2_4 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 52.72/7.01    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 52.72/7.01  fof(f94,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(sK1,k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))) | spl2_4),
% 52.72/7.01    inference(superposition,[],[f92,f35])).
% 52.72/7.01  fof(f92,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl2_4),
% 52.72/7.01    inference(avatar_component_clause,[],[f90])).
% 52.72/7.01  fof(f93,plain,(
% 52.72/7.01    ~spl2_4 | spl2_3),
% 52.72/7.01    inference(avatar_split_clause,[],[f88,f83,f90])).
% 52.72/7.01  fof(f83,plain,(
% 52.72/7.01    spl2_3 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 52.72/7.01    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 52.72/7.01  fof(f88,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl2_3),
% 52.72/7.01    inference(forward_demodulation,[],[f87,f28])).
% 52.72/7.01  fof(f28,plain,(
% 52.72/7.01    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f1])).
% 52.72/7.01  fof(f1,axiom,(
% 52.72/7.01    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 52.72/7.01  fof(f87,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(sK1,sK1,sK1,sK1,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | spl2_3),
% 52.72/7.01    inference(forward_demodulation,[],[f85,f57])).
% 52.72/7.01  fof(f85,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) | spl2_3),
% 52.72/7.01    inference(avatar_component_clause,[],[f83])).
% 52.72/7.01  fof(f86,plain,(
% 52.72/7.01    ~spl2_3),
% 52.72/7.01    inference(avatar_split_clause,[],[f53,f83])).
% 52.72/7.01  fof(f53,plain,(
% 52.72/7.01    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 52.72/7.01    inference(definition_unfolding,[],[f26,f51,f49,f51])).
% 52.72/7.01  fof(f26,plain,(
% 52.72/7.01    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 52.72/7.01    inference(cnf_transformation,[],[f24])).
% 52.72/7.01  fof(f24,plain,(
% 52.72/7.01    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 52.72/7.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 52.72/7.01  fof(f23,plain,(
% 52.72/7.01    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 52.72/7.01    introduced(choice_axiom,[])).
% 52.72/7.01  fof(f20,plain,(
% 52.72/7.01    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 52.72/7.01    inference(ennf_transformation,[],[f19])).
% 52.72/7.01  fof(f19,negated_conjecture,(
% 52.72/7.01    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 52.72/7.01    inference(negated_conjecture,[],[f18])).
% 52.72/7.01  fof(f18,conjecture,(
% 52.72/7.01    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 52.72/7.01  fof(f81,plain,(
% 52.72/7.01    spl2_2 | spl2_1),
% 52.72/7.01    inference(avatar_split_clause,[],[f75,f62,f78])).
% 52.72/7.01  fof(f62,plain,(
% 52.72/7.01    spl2_1 <=> r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 52.72/7.01    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 52.72/7.01  fof(f75,plain,(
% 52.72/7.01    r2_hidden(sK0,sK1) | spl2_1),
% 52.72/7.01    inference(unit_resulting_resolution,[],[f64,f55])).
% 52.72/7.01  fof(f55,plain,(
% 52.72/7.01    ( ! [X0,X1] : (r1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 52.72/7.01    inference(definition_unfolding,[],[f32,f51])).
% 52.72/7.01  fof(f32,plain,(
% 52.72/7.01    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 52.72/7.01    inference(cnf_transformation,[],[f21])).
% 52.72/7.01  fof(f21,plain,(
% 52.72/7.01    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 52.72/7.01    inference(ennf_transformation,[],[f15])).
% 52.72/7.01  fof(f15,axiom,(
% 52.72/7.01    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 52.72/7.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 52.72/7.01  fof(f64,plain,(
% 52.72/7.01    ~r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl2_1),
% 52.72/7.01    inference(avatar_component_clause,[],[f62])).
% 52.72/7.01  fof(f65,plain,(
% 52.72/7.01    ~spl2_1),
% 52.72/7.01    inference(avatar_split_clause,[],[f54,f62])).
% 52.72/7.01  fof(f54,plain,(
% 52.72/7.01    ~r1_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 52.72/7.01    inference(definition_unfolding,[],[f25,f51])).
% 52.72/7.01  fof(f25,plain,(
% 52.72/7.01    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 52.72/7.01    inference(cnf_transformation,[],[f24])).
% 52.72/7.01  % SZS output end Proof for theBenchmark
% 52.72/7.01  % (24546)------------------------------
% 52.72/7.01  % (24546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 52.72/7.01  % (24546)Termination reason: Refutation
% 52.72/7.01  
% 52.72/7.01  % (24546)Memory used [KB]: 134709
% 52.72/7.01  % (24546)Time elapsed: 6.485 s
% 52.72/7.01  % (24546)------------------------------
% 52.72/7.01  % (24546)------------------------------
% 52.72/7.02  % (24530)Success in time 6.643 s
%------------------------------------------------------------------------------
