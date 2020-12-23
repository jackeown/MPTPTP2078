%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t46_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 18.20s
% Output     : Refutation 18.20s
% Verified   : 
% Statistics : Number of formulae       :   35 (  76 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :   37 (  78 expanded)
%              Number of equality atoms :   36 (  77 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(forward_demodulation,[],[f359,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X0,X3)),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(definition_unfolding,[],[f64,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',t45_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',t25_mcart_1)).

fof(f359,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_tarski(sK4,sK5)) ),
    inference(forward_demodulation,[],[f357,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',commutativity_k2_xboole_0)).

fof(f357,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3))),k2_tarski(sK4,sK5)) ),
    inference(superposition,[],[f73,f92])).

fof(f92,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X5,X6)) = k2_zfmisc_1(k2_xboole_0(X5,X7),X6) ),
    inference(superposition,[],[f60,f52])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',t120_zfmisc_1)).

fof(f73,plain,(
    k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(sK4,sK5)),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(forward_demodulation,[],[f72,f69])).

fof(f72,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(backward_demodulation,[],[f69,f71])).

fof(f71,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK5)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(forward_demodulation,[],[f70,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f62,f63,f63])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',t104_enumset1)).

fof(f70,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK5)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(backward_demodulation,[],[f68,f67])).

fof(f67,plain,(
    k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) ),
    inference(definition_unfolding,[],[f45,f58,f66,f59,f59,f59,f59,f59,f59,f59,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',d3_mcart_1)).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f65,f63,f63])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',t65_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',d3_zfmisc_1)).

fof(f45,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f33,f41])).

fof(f41,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) != k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) != k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t46_mcart_1.p',t46_mcart_1)).
%------------------------------------------------------------------------------
