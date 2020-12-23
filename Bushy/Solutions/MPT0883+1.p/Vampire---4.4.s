%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t43_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 19.35s
% Output     : Refutation 19.35s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 218 expanded)
%              Number of leaves         :   12 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :   72 ( 249 expanded)
%              Number of equality atoms :   71 ( 248 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22037,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f22036])).

fof(f22036,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f22035,f381])).

fof(f381,plain,(
    ! [X6,X7,X5] : k2_zfmisc_1(X7,k2_tarski(X5,X6)) = k2_zfmisc_1(X7,k2_tarski(X6,X5)) ),
    inference(forward_demodulation,[],[f375,f329])).

fof(f329,plain,(
    ! [X8,X9] : k2_tarski(X8,X9) = k2_xboole_0(k2_tarski(X8,X8),k2_tarski(X9,X9)) ),
    inference(superposition,[],[f68,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',idempotence_k2_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f64,f65,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',t45_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',t104_enumset1)).

fof(f375,plain,(
    ! [X6,X7,X5] : k2_zfmisc_1(X7,k2_tarski(X5,X6)) = k2_zfmisc_1(X7,k2_xboole_0(k2_tarski(X6,X6),k2_tarski(X5,X5))) ),
    inference(superposition,[],[f153,f329])).

fof(f153,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_zfmisc_1(X7,k2_xboole_0(X9,X8)) ),
    inference(superposition,[],[f101,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',t120_zfmisc_1)).

fof(f101,plain,(
    ! [X8,X7,X9] : k2_xboole_0(k2_zfmisc_1(X7,X9),k2_zfmisc_1(X7,X8)) = k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f61,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',commutativity_k2_xboole_0)).

fof(f22035,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK3,sK2)),k1_tarski(sK4)) ),
    inference(backward_demodulation,[],[f21977,f742])).

fof(f742,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f741,f61])).

fof(f741,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK3))),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f739,f52])).

fof(f739,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK3)),k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2))),k1_tarski(sK4)) ),
    inference(superposition,[],[f73,f94])).

fof(f94,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X5,X6)) = k2_zfmisc_1(k2_xboole_0(X5,X7),X6) ),
    inference(superposition,[],[f60,f52])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK3)),k1_tarski(sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f72,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',t36_zfmisc_1)).

fof(f72,plain,(
    k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK3)),k1_tarski(sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f71,f63])).

fof(f71,plain,(
    k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK3)),k1_tarski(sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f70,f63])).

fof(f70,plain,(
    k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK3),k4_tarski(sK1,sK3)),k1_tarski(sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(backward_demodulation,[],[f63,f67])).

fof(f67,plain,(
    k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k1_tarski(sK4)) ),
    inference(definition_unfolding,[],[f45,f58,f65,f59,f59,f59,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',d3_mcart_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',d3_zfmisc_1)).

fof(f45,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',t43_mcart_1)).

fof(f21977,plain,(
    ! [X12,X10,X13,X11] : k2_zfmisc_1(k2_tarski(X10,X11),k2_tarski(X13,X12)) = k2_zfmisc_1(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),k1_tarski(X13))) ),
    inference(superposition,[],[f18305,f4913])).

fof(f4913,plain,(
    ! [X68,X66,X69,X67] : k2_zfmisc_1(k2_tarski(X66,X67),k2_xboole_0(X69,k1_tarski(X68))) = k2_zfmisc_1(k2_tarski(X66,X67),k2_xboole_0(X69,k2_tarski(X68,X68))) ),
    inference(forward_demodulation,[],[f4897,f300])).

fof(f300,plain,(
    ! [X14,X17,X15,X16] : k2_xboole_0(k2_zfmisc_1(k2_tarski(X14,X15),X17),k2_zfmisc_1(k2_tarski(X15,X14),k1_tarski(X16))) = k2_zfmisc_1(k2_tarski(X14,X15),k2_xboole_0(X17,k1_tarski(X16))) ),
    inference(superposition,[],[f61,f277])).

fof(f277,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k2_tarski(X7,X9),k1_tarski(X8)) = k2_zfmisc_1(k2_tarski(X9,X7),k1_tarski(X8)) ),
    inference(superposition,[],[f214,f63])).

fof(f214,plain,(
    ! [X6,X7,X5] : k2_tarski(k4_tarski(X7,X6),k4_tarski(X5,X6)) = k2_zfmisc_1(k2_tarski(X5,X7),k1_tarski(X6)) ),
    inference(superposition,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',commutativity_k2_tarski)).

fof(f4897,plain,(
    ! [X68,X66,X69,X67] : k2_xboole_0(k2_zfmisc_1(k2_tarski(X66,X67),X69),k2_zfmisc_1(k2_tarski(X67,X66),k1_tarski(X68))) = k2_zfmisc_1(k2_tarski(X66,X67),k2_xboole_0(X69,k2_tarski(X68,X68))) ),
    inference(superposition,[],[f61,f4844])).

fof(f4844,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X2,X0),k1_tarski(X1)) = k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) ),
    inference(forward_demodulation,[],[f4842,f63])).

fof(f4842,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X2,X1),k4_tarski(X0,X1)) = k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) ),
    inference(backward_demodulation,[],[f4816,f1918])).

fof(f1918,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(k1_tarski(X2),k2_tarski(X1,X1)),k2_zfmisc_1(k2_tarski(X0,X0),k1_tarski(X1))) = k2_zfmisc_1(k2_tarski(X0,X2),k2_tarski(X1,X1)) ),
    inference(superposition,[],[f524,f213])).

fof(f213,plain,(
    ! [X0,X1] : k2_zfmisc_1(k2_tarski(X0,X0),k1_tarski(X1)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X1)) ),
    inference(superposition,[],[f63,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f524,plain,(
    ! [X24,X23,X21,X22] : k2_xboole_0(k2_zfmisc_1(k1_tarski(X24),k2_tarski(X22,X23)),k2_zfmisc_1(k1_tarski(X21),k2_tarski(X22,X23))) = k2_zfmisc_1(k2_tarski(X21,X24),k2_tarski(X22,X23)) ),
    inference(superposition,[],[f75,f52])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),k2_tarski(X2,X3)),k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f74,f62])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X0,X3)),k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f69,f62])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X0,X3)),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t43_mcart_1.p',t25_mcart_1)).

fof(f4816,plain,(
    ! [X14,X17,X15,X16] : k2_tarski(k4_tarski(X16,X17),k4_tarski(X14,X15)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X16),k2_tarski(X17,X17)),k2_zfmisc_1(k2_tarski(X14,X14),k1_tarski(X15))) ),
    inference(superposition,[],[f361,f214])).

fof(f361,plain,(
    ! [X6,X4,X5] : k2_tarski(k4_tarski(X4,X5),X6) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X4),k2_tarski(X5,X5)),k2_tarski(X6,X6)) ),
    inference(superposition,[],[f329,f209])).

fof(f209,plain,(
    ! [X4,X5,X3] : k2_tarski(k4_tarski(X3,X5),k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f62,f51])).

fof(f18305,plain,(
    ! [X161,X159,X162,X160] : k2_zfmisc_1(k2_tarski(X161,X162),k2_tarski(X160,X159)) = k2_zfmisc_1(k2_tarski(X161,X162),k2_xboole_0(k1_tarski(X159),k2_tarski(X160,X160))) ),
    inference(superposition,[],[f4912,f371])).

fof(f371,plain,(
    ! [X8,X7] : k2_tarski(X7,X8) = k2_xboole_0(k2_tarski(X8,X8),k2_tarski(X7,X7)) ),
    inference(superposition,[],[f329,f52])).

fof(f4912,plain,(
    ! [X64,X62,X65,X63] : k2_zfmisc_1(k2_tarski(X62,X63),k2_xboole_0(k1_tarski(X64),X65)) = k2_zfmisc_1(k2_tarski(X62,X63),k2_xboole_0(k2_tarski(X64,X64),X65)) ),
    inference(forward_demodulation,[],[f4896,f299])).

fof(f299,plain,(
    ! [X12,X10,X13,X11] : k2_xboole_0(k2_zfmisc_1(k2_tarski(X11,X10),k1_tarski(X12)),k2_zfmisc_1(k2_tarski(X10,X11),X13)) = k2_zfmisc_1(k2_tarski(X10,X11),k2_xboole_0(k1_tarski(X12),X13)) ),
    inference(superposition,[],[f61,f277])).

fof(f4896,plain,(
    ! [X64,X62,X65,X63] : k2_xboole_0(k2_zfmisc_1(k2_tarski(X63,X62),k1_tarski(X64)),k2_zfmisc_1(k2_tarski(X62,X63),X65)) = k2_zfmisc_1(k2_tarski(X62,X63),k2_xboole_0(k2_tarski(X64,X64),X65)) ),
    inference(superposition,[],[f61,f4844])).
%------------------------------------------------------------------------------
