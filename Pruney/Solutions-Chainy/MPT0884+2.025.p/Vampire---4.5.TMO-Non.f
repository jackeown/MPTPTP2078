%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:58 EST 2020

% Result     : Timeout 59.96s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :   60 ( 276 expanded)
%              Number of leaves         :   17 ( 103 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 283 expanded)
%              Number of equality atoms :   58 ( 274 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22728,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f22727])).

fof(f22727,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f22726])).

fof(f22726,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f22717,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k2_enumset1(k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(k4_tarski(X2,X1),X3),k4_tarski(k4_tarski(X2,X1),X4)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X3,X3,X3,X4)) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f32,f40,f43,f40])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f34,f40,f40])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f22717,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))
    | spl5_1 ),
    inference(superposition,[],[f64,f17703])).

fof(f17703,plain,(
    ! [X47,X48,X46,X49] : k2_enumset1(X46,X47,X48,X49) = k2_enumset1(X46,X48,X47,X49) ),
    inference(superposition,[],[f1770,f208])).

fof(f208,plain,(
    ! [X14,X17,X15,X16] : k2_enumset1(X16,X17,X14,X15) = k3_tarski(k2_enumset1(k2_enumset1(X16,X16,X16,X17),k2_enumset1(X16,X16,X16,X17),k2_enumset1(X16,X16,X16,X17),k2_enumset1(X14,X15,X15,X14))) ),
    inference(superposition,[],[f96,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X0,X1,X1,X0) ),
    inference(superposition,[],[f49,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f33,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) ),
    inference(definition_unfolding,[],[f35,f41,f40,f28])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f40])).

fof(f25,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X1,X1,X1,X0),k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X0))) ),
    inference(definition_unfolding,[],[f30,f28,f41,f40,f40])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) ),
    inference(superposition,[],[f53,f46])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X4))) ),
    inference(definition_unfolding,[],[f36,f42,f41,f28,f40])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f1770,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k3_tarski(k2_enumset1(k2_enumset1(X3,X3,X3,X5),k2_enumset1(X3,X3,X3,X5),k2_enumset1(X3,X3,X3,X5),k2_enumset1(X4,X6,X6,X4))) ),
    inference(superposition,[],[f134,f46])).

fof(f134,plain,(
    ! [X14,X12,X15,X13,X11] : k3_tarski(k2_enumset1(k2_enumset1(X14,X14,X15,X11),k2_enumset1(X14,X14,X15,X11),k2_enumset1(X14,X14,X15,X11),k2_enumset1(X12,X13,X13,X12))) = k3_tarski(k2_enumset1(k2_enumset1(X14,X14,X14,X15),k2_enumset1(X14,X14,X14,X15),k2_enumset1(X14,X14,X14,X15),k2_enumset1(X12,X12,X11,X13))) ),
    inference(superposition,[],[f54,f49])).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k3_tarski(k2_enumset1(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X4,X4,X5,X6))))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f39,f45,f41,f28])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k3_tarski(k2_enumset1(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X4,X4,X5,X6))))) ),
    inference(definition_unfolding,[],[f38,f41,f40,f42])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f64,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f65,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f47,f62])).

fof(f47,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    inference(definition_unfolding,[],[f22,f26,f40,f43,f40,f27,f27,f27,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f22,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : run_vampire %s %d
% 0.11/0.30  % Computer   : n014.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 10:09:37 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.40  % (6528)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.16/0.40  % (6540)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.16/0.41  % (6526)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.16/0.42  % (6527)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.16/0.42  % (6537)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.16/0.43  % (6533)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.16/0.43  % (6536)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.16/0.44  % (6536)Refutation not found, incomplete strategy% (6536)------------------------------
% 0.16/0.44  % (6536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.44  % (6536)Termination reason: Refutation not found, incomplete strategy
% 0.16/0.44  
% 0.16/0.44  % (6536)Memory used [KB]: 10618
% 0.16/0.44  % (6536)Time elapsed: 0.061 s
% 0.16/0.44  % (6536)------------------------------
% 0.16/0.44  % (6536)------------------------------
% 0.16/0.44  % (6529)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.16/0.44  % (6538)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.16/0.45  % (6530)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.16/0.45  % (6534)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.16/0.46  % (6532)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.16/0.46  % (6525)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.16/0.46  % (6535)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.16/0.46  % (6542)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.16/0.47  % (6531)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.16/0.48  % (6541)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.16/0.48  % (6539)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 5.53/1.03  % (6529)Time limit reached!
% 5.53/1.03  % (6529)------------------------------
% 5.53/1.03  % (6529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.53/1.03  % (6529)Termination reason: Time limit
% 5.53/1.03  
% 5.53/1.03  % (6529)Memory used [KB]: 11385
% 5.53/1.03  % (6529)Time elapsed: 0.622 s
% 5.53/1.03  % (6529)------------------------------
% 5.53/1.03  % (6529)------------------------------
% 11.97/1.89  % (6531)Time limit reached!
% 11.97/1.89  % (6531)------------------------------
% 11.97/1.89  % (6531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.97/1.89  % (6531)Termination reason: Time limit
% 11.97/1.89  % (6531)Termination phase: Saturation
% 11.97/1.89  
% 11.97/1.89  % (6531)Memory used [KB]: 26481
% 11.97/1.89  % (6531)Time elapsed: 1.500 s
% 11.97/1.89  % (6531)------------------------------
% 11.97/1.89  % (6531)------------------------------
% 12.62/1.92  % (6530)Time limit reached!
% 12.62/1.92  % (6530)------------------------------
% 12.62/1.92  % (6530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.62/1.92  % (6530)Termination reason: Time limit
% 12.62/1.92  
% 12.62/1.92  % (6530)Memory used [KB]: 30958
% 12.62/1.92  % (6530)Time elapsed: 1.528 s
% 12.62/1.92  % (6530)------------------------------
% 12.62/1.92  % (6530)------------------------------
% 14.42/2.19  % (6527)Time limit reached!
% 14.42/2.19  % (6527)------------------------------
% 14.42/2.19  % (6527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.42/2.19  % (6527)Termination reason: Time limit
% 14.42/2.19  % (6527)Termination phase: Saturation
% 14.42/2.19  
% 14.42/2.19  % (6527)Memory used [KB]: 15735
% 14.42/2.19  % (6527)Time elapsed: 1.800 s
% 14.42/2.19  % (6527)------------------------------
% 14.42/2.19  % (6527)------------------------------
% 17.52/2.57  % (6537)Time limit reached!
% 17.52/2.57  % (6537)------------------------------
% 17.52/2.57  % (6537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.52/2.58  % (6537)Termination reason: Time limit
% 17.52/2.58  % (6537)Termination phase: Saturation
% 17.52/2.58  
% 17.52/2.58  % (6537)Memory used [KB]: 13816
% 17.52/2.58  % (6537)Time elapsed: 2.200 s
% 17.52/2.58  % (6537)------------------------------
% 17.52/2.58  % (6537)------------------------------
% 59.96/7.86  % (6540)Refutation found. Thanks to Tanya!
% 59.96/7.86  % SZS status Theorem for theBenchmark
% 59.96/7.87  % SZS output start Proof for theBenchmark
% 59.96/7.87  fof(f22728,plain,(
% 59.96/7.87    $false),
% 59.96/7.87    inference(avatar_sat_refutation,[],[f65,f22727])).
% 59.96/7.87  fof(f22727,plain,(
% 59.96/7.87    spl5_1),
% 59.96/7.87    inference(avatar_contradiction_clause,[],[f22726])).
% 59.96/7.87  fof(f22726,plain,(
% 59.96/7.87    $false | spl5_1),
% 59.96/7.87    inference(subsumption_resolution,[],[f22717,f55])).
% 59.96/7.87  fof(f55,plain,(
% 59.96/7.87    ( ! [X4,X2,X0,X3,X1] : (k2_enumset1(k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(k4_tarski(X2,X1),X3),k4_tarski(k4_tarski(X2,X1),X4)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X2),k2_enumset1(X1,X1,X1,X1)),k2_enumset1(X3,X3,X3,X4))) )),
% 59.96/7.87    inference(superposition,[],[f52,f50])).
% 59.96/7.87  fof(f50,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X2)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f32,f40,f43,f40])).
% 59.96/7.87  fof(f43,plain,(
% 59.96/7.87    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 59.96/7.87    inference(definition_unfolding,[],[f23,f40])).
% 59.96/7.87  fof(f23,plain,(
% 59.96/7.87    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f8])).
% 59.96/7.87  fof(f8,axiom,(
% 59.96/7.87    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 59.96/7.87  fof(f40,plain,(
% 59.96/7.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 59.96/7.87    inference(definition_unfolding,[],[f24,f28])).
% 59.96/7.87  fof(f28,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f10])).
% 59.96/7.87  fof(f10,axiom,(
% 59.96/7.87    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 59.96/7.87  fof(f24,plain,(
% 59.96/7.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f9])).
% 59.96/7.87  fof(f9,axiom,(
% 59.96/7.87    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 59.96/7.87  fof(f32,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f14])).
% 59.96/7.87  fof(f14,axiom,(
% 59.96/7.87    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 59.96/7.87  fof(f52,plain,(
% 59.96/7.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f34,f40,f40])).
% 59.96/7.87  fof(f34,plain,(
% 59.96/7.87    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f13])).
% 59.96/7.87  fof(f13,axiom,(
% 59.96/7.87    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 59.96/7.87  fof(f22717,plain,(
% 59.96/7.87    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)) | spl5_1),
% 59.96/7.87    inference(superposition,[],[f64,f17703])).
% 59.96/7.87  fof(f17703,plain,(
% 59.96/7.87    ( ! [X47,X48,X46,X49] : (k2_enumset1(X46,X47,X48,X49) = k2_enumset1(X46,X48,X47,X49)) )),
% 59.96/7.87    inference(superposition,[],[f1770,f208])).
% 59.96/7.87  fof(f208,plain,(
% 59.96/7.87    ( ! [X14,X17,X15,X16] : (k2_enumset1(X16,X17,X14,X15) = k3_tarski(k2_enumset1(k2_enumset1(X16,X16,X16,X17),k2_enumset1(X16,X16,X16,X17),k2_enumset1(X16,X16,X16,X17),k2_enumset1(X14,X15,X15,X14)))) )),
% 59.96/7.87    inference(superposition,[],[f96,f86])).
% 59.96/7.87  fof(f86,plain,(
% 59.96/7.87    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X0,X1,X1,X0)) )),
% 59.96/7.87    inference(superposition,[],[f49,f46])).
% 59.96/7.87  fof(f46,plain,(
% 59.96/7.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X2,X3)))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f33,f42])).
% 59.96/7.87  fof(f42,plain,(
% 59.96/7.87    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4)))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f35,f41,f40,f28])).
% 59.96/7.87  fof(f41,plain,(
% 59.96/7.87    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f25,f40])).
% 59.96/7.87  fof(f25,plain,(
% 59.96/7.87    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f12])).
% 59.96/7.87  fof(f12,axiom,(
% 59.96/7.87    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 59.96/7.87  fof(f35,plain,(
% 59.96/7.87    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f4])).
% 59.96/7.87  fof(f4,axiom,(
% 59.96/7.87    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 59.96/7.87  fof(f33,plain,(
% 59.96/7.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f11])).
% 59.96/7.87  fof(f11,axiom,(
% 59.96/7.87    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 59.96/7.87  fof(f49,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_enumset1(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X1,X1,X1,X0),k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X0)))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f30,f28,f41,f40,f40])).
% 59.96/7.87  fof(f30,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f2])).
% 59.96/7.87  fof(f2,axiom,(
% 59.96/7.87    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 59.96/7.87  fof(f96,plain,(
% 59.96/7.87    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)))) )),
% 59.96/7.87    inference(superposition,[],[f53,f46])).
% 59.96/7.87  fof(f53,plain,(
% 59.96/7.87    ( ! [X4,X2,X0,X3,X1] : (k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X3,X4))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X4)))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f36,f42,f41,f28,f40])).
% 59.96/7.87  fof(f36,plain,(
% 59.96/7.87    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f1])).
% 59.96/7.87  fof(f1,axiom,(
% 59.96/7.87    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 59.96/7.87  fof(f1770,plain,(
% 59.96/7.87    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k3_tarski(k2_enumset1(k2_enumset1(X3,X3,X3,X5),k2_enumset1(X3,X3,X3,X5),k2_enumset1(X3,X3,X3,X5),k2_enumset1(X4,X6,X6,X4)))) )),
% 59.96/7.87    inference(superposition,[],[f134,f46])).
% 59.96/7.87  fof(f134,plain,(
% 59.96/7.87    ( ! [X14,X12,X15,X13,X11] : (k3_tarski(k2_enumset1(k2_enumset1(X14,X14,X15,X11),k2_enumset1(X14,X14,X15,X11),k2_enumset1(X14,X14,X15,X11),k2_enumset1(X12,X13,X13,X12))) = k3_tarski(k2_enumset1(k2_enumset1(X14,X14,X14,X15),k2_enumset1(X14,X14,X14,X15),k2_enumset1(X14,X14,X14,X15),k2_enumset1(X12,X12,X11,X13)))) )),
% 59.96/7.87    inference(superposition,[],[f54,f49])).
% 59.96/7.87  fof(f54,plain,(
% 59.96/7.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k3_tarski(k2_enumset1(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X4,X4,X5,X6))))) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X4,X5,X6)))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f39,f45,f41,f28])).
% 59.96/7.87  fof(f45,plain,(
% 59.96/7.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k2_enumset1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k2_enumset1(X0,X0,X0,X1),k3_tarski(k2_enumset1(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X2,X2,X2,X3),k2_enumset1(X4,X4,X5,X6)))))) )),
% 59.96/7.87    inference(definition_unfolding,[],[f38,f41,f40,f42])).
% 59.96/7.87  fof(f38,plain,(
% 59.96/7.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f6])).
% 59.96/7.87  fof(f6,axiom,(
% 59.96/7.87    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 59.96/7.87  fof(f39,plain,(
% 59.96/7.87    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 59.96/7.87    inference(cnf_transformation,[],[f7])).
% 59.96/7.87  fof(f7,axiom,(
% 59.96/7.87    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 59.96/7.87  fof(f64,plain,(
% 59.96/7.87    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) | spl5_1),
% 59.96/7.87    inference(avatar_component_clause,[],[f62])).
% 59.96/7.87  fof(f62,plain,(
% 59.96/7.87    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 59.96/7.87    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 59.96/7.87  fof(f65,plain,(
% 59.96/7.87    ~spl5_1),
% 59.96/7.87    inference(avatar_split_clause,[],[f47,f62])).
% 59.96/7.87  fof(f47,plain,(
% 59.96/7.87    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 59.96/7.87    inference(definition_unfolding,[],[f22,f26,f40,f43,f40,f27,f27,f27,f27])).
% 59.96/7.87  fof(f27,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f15])).
% 59.96/7.87  fof(f15,axiom,(
% 59.96/7.87    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 59.96/7.87  fof(f26,plain,(
% 59.96/7.87    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 59.96/7.87    inference(cnf_transformation,[],[f16])).
% 59.96/7.87  fof(f16,axiom,(
% 59.96/7.87    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 59.96/7.87  fof(f22,plain,(
% 59.96/7.87    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 59.96/7.87    inference(cnf_transformation,[],[f21])).
% 59.96/7.87  fof(f21,plain,(
% 59.96/7.87    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 59.96/7.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f20])).
% 59.96/7.87  fof(f20,plain,(
% 59.96/7.87    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 59.96/7.87    introduced(choice_axiom,[])).
% 59.96/7.87  fof(f19,plain,(
% 59.96/7.87    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 59.96/7.87    inference(ennf_transformation,[],[f18])).
% 59.96/7.87  fof(f18,negated_conjecture,(
% 59.96/7.87    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 59.96/7.87    inference(negated_conjecture,[],[f17])).
% 59.96/7.87  fof(f17,conjecture,(
% 59.96/7.87    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 59.96/7.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 59.96/7.87  % SZS output end Proof for theBenchmark
% 59.96/7.87  % (6540)------------------------------
% 59.96/7.87  % (6540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 59.96/7.87  % (6540)Termination reason: Refutation
% 59.96/7.87  
% 59.96/7.87  % (6540)Memory used [KB]: 139955
% 59.96/7.87  % (6540)Time elapsed: 7.453 s
% 59.96/7.87  % (6540)------------------------------
% 59.96/7.87  % (6540)------------------------------
% 59.96/7.88  % (6522)Success in time 7.562 s
%------------------------------------------------------------------------------
