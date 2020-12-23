%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:23 EST 2020

% Result     : Theorem 7.96s
% Output     : Refutation 7.96s
% Verified   : 
% Statistics : Number of formulae       :  130 (4537 expanded)
%              Number of leaves         :   18 (1449 expanded)
%              Depth                    :   38
%              Number of atoms          :  265 (5655 expanded)
%              Number of equality atoms :  192 (4959 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7856,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7832,f74])).

fof(f74,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f42,f37])).

fof(f37,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f7832,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f335,f7808])).

fof(f7808,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f7807,f7165])).

fof(f7165,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9 ),
    inference(superposition,[],[f6733,f6668])).

fof(f6668,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f6653,f76])).

fof(f76,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f44,f40])).

fof(f40,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f6653,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f468,f6632])).

fof(f6632,plain,(
    ! [X11] : k1_xboole_0 = k3_xboole_0(X11,k1_xboole_0) ),
    inference(backward_demodulation,[],[f674,f6599])).

fof(f6599,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f104,f6563])).

fof(f6563,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f6245,f6417])).

fof(f6417,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f118,f6291])).

fof(f6291,plain,(
    ! [X4] : k3_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(forward_demodulation,[],[f6290,f6245])).

fof(f6290,plain,(
    ! [X4] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(forward_demodulation,[],[f6289,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6289,plain,(
    ! [X4] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) ),
    inference(forward_demodulation,[],[f6283,f202])).

fof(f202,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X9,X9) ),
    inference(forward_demodulation,[],[f195,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f195,plain,(
    ! [X9] : k3_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X9,k2_xboole_0(X9,k1_xboole_0)) ),
    inference(superposition,[],[f48,f40])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f6283,plain,(
    ! [X4] : k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),k3_xboole_0(k1_xboole_0,X4)) ),
    inference(superposition,[],[f99,f6245])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f46,f43])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f88,f113])).

fof(f113,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f47,f76])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(unit_resulting_resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f6245,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f6175,f43])).

fof(f6175,plain,(
    ! [X4] : k3_xboole_0(k1_xboole_0,X4) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X4,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6174,f2559])).

fof(f2559,plain,(
    ! [X79] : k3_xboole_0(k1_xboole_0,X79) = k5_xboole_0(X79,k4_xboole_0(X79,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2558,f1145])).

fof(f1145,plain,(
    ! [X0] : k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X0)) = X0 ),
    inference(forward_demodulation,[],[f1140,f76])).

fof(f1140,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X0)) ),
    inference(superposition,[],[f213,f1044])).

fof(f1044,plain,(
    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f1043,f756])).

fof(f756,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(superposition,[],[f118,f755])).

fof(f755,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f476,f721])).

fof(f721,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f720,f115])).

fof(f115,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(forward_demodulation,[],[f111,f39])).

fof(f111,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f47,f104])).

fof(f720,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,k1_tarski(sK0))) ),
    inference(superposition,[],[f47,f477])).

fof(f477,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f463,f43])).

fof(f463,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f103,f202])).

fof(f103,plain,(
    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f46,f90])).

fof(f90,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f74,f49])).

fof(f476,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f462,f46])).

fof(f462,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_xboole_0)) ),
    inference(backward_demodulation,[],[f110,f202])).

fof(f110,plain,(
    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(superposition,[],[f47,f103])).

fof(f1043,plain,(
    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f1039,f40])).

fof(f1039,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_xboole_0),k1_tarski(sK0)) ),
    inference(superposition,[],[f190,f759])).

fof(f759,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f758,f76])).

fof(f758,plain,(
    k2_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k1_xboole_0,k1_tarski(sK0)) ),
    inference(superposition,[],[f47,f755])).

fof(f190,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f48,f44])).

fof(f213,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f54,f44])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2558,plain,(
    ! [X79] : k3_xboole_0(k1_xboole_0,X79) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X79)),k4_xboole_0(X79,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f2493,f113])).

fof(f2493,plain,(
    ! [X79] : k3_xboole_0(k1_xboole_0,X79) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X79)),k2_xboole_0(k1_xboole_0,X79)) ),
    inference(superposition,[],[f235,f1044])).

fof(f235,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X4)),k2_xboole_0(k5_xboole_0(X2,X3),X4)) ),
    inference(superposition,[],[f48,f54])).

fof(f6174,plain,(
    ! [X4] : k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X4,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6173,f43])).

fof(f6173,plain,(
    ! [X4] : k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f5960,f46])).

fof(f5960,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0))) ),
    inference(superposition,[],[f468,f202])).

fof(f104,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f46,f76])).

fof(f674,plain,(
    ! [X11] : k3_xboole_0(X11,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X11) ),
    inference(superposition,[],[f99,f76])).

fof(f468,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[],[f54,f202])).

fof(f6733,plain,(
    ! [X14,X13] : k5_xboole_0(X13,k5_xboole_0(X14,X13)) = X14 ),
    inference(forward_demodulation,[],[f6693,f40])).

fof(f6693,plain,(
    ! [X14,X13] : k5_xboole_0(X14,k1_xboole_0) = k5_xboole_0(X13,k5_xboole_0(X14,X13)) ),
    inference(superposition,[],[f227,f6652])).

fof(f6652,plain,(
    ! [X9] : k1_xboole_0 = k5_xboole_0(X9,X9) ),
    inference(backward_demodulation,[],[f202,f6632])).

fof(f227,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7)) ),
    inference(superposition,[],[f54,f44])).

fof(f7807,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f7778,f1126])).

fof(f1126,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f1125,f40])).

fof(f1125,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1124,f756])).

fof(f1124,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_xboole_0,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f1123,f43])).

fof(f1123,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1090,f202])).

fof(f1090,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(superposition,[],[f213,f199])).

fof(f199,plain,(
    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(superposition,[],[f48,f37])).

fof(f7778,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f2284,f7041])).

fof(f7041,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f6668,f46])).

fof(f2284,plain,(
    ! [X66] : k2_xboole_0(k1_tarski(sK1),X66) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(X66,k1_tarski(sK1)))) ),
    inference(superposition,[],[f231,f1386])).

fof(f1386,plain,(
    k1_tarski(sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f199,f1126])).

fof(f231,plain,(
    ! [X17,X18,X16] : k2_xboole_0(k5_xboole_0(X16,X17),X18) = k5_xboole_0(X16,k5_xboole_0(X17,k4_xboole_0(X18,k5_xboole_0(X16,X17)))) ),
    inference(superposition,[],[f54,f47])).

fof(f335,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k1_tarski(sK1),X0),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f137,f322,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f322,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f321,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f321,plain,(
    ~ r2_hidden(sK1,k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f305,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f305,plain,(
    ~ r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f38,f38,f38,f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r2_hidden(X5,k1_enumset1(X0,X1,X2))
      | X1 = X5
      | X0 = X5
      | X2 = X5 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f38,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f137,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1)) ),
    inference(unit_resulting_resolution,[],[f42,f87,f50])).

fof(f87,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f84,f41])).

fof(f84,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f72,f45])).

fof(f72,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (32510)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (32525)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.50  % (32503)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (32511)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (32517)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (32509)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (32518)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (32503)Refutation not found, incomplete strategy% (32503)------------------------------
% 0.22/0.51  % (32503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32503)Memory used [KB]: 1663
% 0.22/0.51  % (32503)Time elapsed: 0.102 s
% 0.22/0.51  % (32503)------------------------------
% 0.22/0.51  % (32503)------------------------------
% 0.22/0.51  % (32519)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (32508)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (32507)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (32526)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (32512)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (32512)Refutation not found, incomplete strategy% (32512)------------------------------
% 0.22/0.53  % (32512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32512)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32512)Memory used [KB]: 10618
% 0.22/0.53  % (32512)Time elapsed: 0.111 s
% 0.22/0.53  % (32512)------------------------------
% 0.22/0.53  % (32512)------------------------------
% 0.22/0.53  % (32506)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (32531)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (32529)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.53  % (32516)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (32505)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (32520)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (32520)Refutation not found, incomplete strategy% (32520)------------------------------
% 0.22/0.54  % (32520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32520)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32520)Memory used [KB]: 10618
% 0.22/0.54  % (32520)Time elapsed: 0.131 s
% 0.22/0.54  % (32520)------------------------------
% 0.22/0.54  % (32520)------------------------------
% 0.22/0.54  % (32532)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (32515)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (32521)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (32513)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (32504)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (32513)Refutation not found, incomplete strategy% (32513)------------------------------
% 0.22/0.55  % (32513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (32513)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (32513)Memory used [KB]: 10618
% 0.22/0.55  % (32513)Time elapsed: 0.149 s
% 0.22/0.55  % (32513)------------------------------
% 0.22/0.55  % (32513)------------------------------
% 0.22/0.55  % (32514)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (32523)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (32524)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (32527)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (32528)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.56  % (32530)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.57  % (32522)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.57  % (32514)Refutation not found, incomplete strategy% (32514)------------------------------
% 0.22/0.57  % (32514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (32514)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (32514)Memory used [KB]: 10618
% 0.22/0.57  % (32514)Time elapsed: 0.172 s
% 0.22/0.57  % (32514)------------------------------
% 0.22/0.57  % (32514)------------------------------
% 2.00/0.62  % (32534)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.62  % (32534)Refutation not found, incomplete strategy% (32534)------------------------------
% 2.00/0.62  % (32534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.00/0.62  % (32534)Termination reason: Refutation not found, incomplete strategy
% 2.00/0.62  
% 2.00/0.62  % (32534)Memory used [KB]: 6140
% 2.00/0.62  % (32534)Time elapsed: 0.051 s
% 2.00/0.62  % (32534)------------------------------
% 2.00/0.62  % (32534)------------------------------
% 2.11/0.67  % (32535)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.68  % (32536)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.69  % (32537)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.70  % (32538)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.75/0.74  % (32539)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 3.28/0.81  % (32535)Refutation not found, incomplete strategy% (32535)------------------------------
% 3.28/0.81  % (32535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.81  % (32535)Termination reason: Refutation not found, incomplete strategy
% 3.28/0.81  
% 3.28/0.81  % (32535)Memory used [KB]: 6140
% 3.28/0.81  % (32535)Time elapsed: 0.236 s
% 3.28/0.81  % (32535)------------------------------
% 3.28/0.81  % (32535)------------------------------
% 3.28/0.82  % (32508)Time limit reached!
% 3.28/0.82  % (32508)------------------------------
% 3.28/0.82  % (32508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.82  % (32508)Termination reason: Time limit
% 3.28/0.82  
% 3.28/0.82  % (32508)Memory used [KB]: 8827
% 3.28/0.82  % (32508)Time elapsed: 0.405 s
% 3.28/0.82  % (32508)------------------------------
% 3.28/0.82  % (32508)------------------------------
% 4.34/0.94  % (32504)Time limit reached!
% 4.34/0.94  % (32504)------------------------------
% 4.34/0.94  % (32504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.94  % (32504)Termination reason: Time limit
% 4.34/0.94  
% 4.34/0.94  % (32504)Memory used [KB]: 9338
% 4.34/0.94  % (32504)Time elapsed: 0.515 s
% 4.34/0.94  % (32504)------------------------------
% 4.34/0.94  % (32504)------------------------------
% 4.34/0.95  % (32540)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.34/0.96  % (32515)Time limit reached!
% 4.34/0.96  % (32515)------------------------------
% 4.34/0.96  % (32515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.96  % (32515)Termination reason: Time limit
% 4.34/0.96  % (32515)Termination phase: Saturation
% 4.34/0.96  
% 4.34/0.96  % (32515)Memory used [KB]: 10746
% 4.34/0.96  % (32515)Time elapsed: 0.500 s
% 4.34/0.96  % (32515)------------------------------
% 4.34/0.96  % (32515)------------------------------
% 4.34/0.97  % (32541)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.34/1.00  % (32537)Time limit reached!
% 4.34/1.00  % (32537)------------------------------
% 4.34/1.00  % (32537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/1.00  % (32537)Termination reason: Time limit
% 4.34/1.00  % (32537)Termination phase: Saturation
% 4.34/1.00  
% 4.34/1.00  % (32537)Memory used [KB]: 7675
% 4.34/1.00  % (32537)Time elapsed: 0.400 s
% 4.34/1.00  % (32537)------------------------------
% 4.34/1.00  % (32537)------------------------------
% 4.34/1.01  % (32538)Time limit reached!
% 4.34/1.01  % (32538)------------------------------
% 4.34/1.01  % (32538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/1.01  % (32538)Termination reason: Time limit
% 4.34/1.01  
% 4.34/1.01  % (32538)Memory used [KB]: 13944
% 4.34/1.01  % (32538)Time elapsed: 0.411 s
% 4.34/1.01  % (32538)------------------------------
% 4.34/1.01  % (32538)------------------------------
% 4.83/1.02  % (32519)Time limit reached!
% 4.83/1.02  % (32519)------------------------------
% 4.83/1.02  % (32519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.83/1.02  % (32519)Termination reason: Time limit
% 4.83/1.02  
% 4.83/1.02  % (32519)Memory used [KB]: 19317
% 4.83/1.02  % (32519)Time elapsed: 0.618 s
% 4.83/1.02  % (32519)------------------------------
% 4.83/1.02  % (32519)------------------------------
% 4.83/1.04  % (32542)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.83/1.04  % (32510)Time limit reached!
% 4.83/1.04  % (32510)------------------------------
% 4.83/1.04  % (32510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.83/1.05  % (32510)Termination reason: Time limit
% 4.83/1.05  
% 4.83/1.05  % (32510)Memory used [KB]: 10874
% 4.83/1.05  % (32510)Time elapsed: 0.622 s
% 4.83/1.05  % (32510)------------------------------
% 4.83/1.05  % (32510)------------------------------
% 4.83/1.06  % (32531)Time limit reached!
% 4.83/1.06  % (32531)------------------------------
% 4.83/1.06  % (32531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.83/1.06  % (32531)Termination reason: Time limit
% 4.83/1.06  
% 4.83/1.06  % (32531)Memory used [KB]: 10874
% 4.83/1.06  % (32531)Time elapsed: 0.643 s
% 4.83/1.06  % (32531)------------------------------
% 4.83/1.06  % (32531)------------------------------
% 5.41/1.08  % (32543)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.41/1.12  % (32544)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.41/1.14  % (32545)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 5.41/1.16  % (32546)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.41/1.17  % (32547)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 6.58/1.20  % (32548)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 6.58/1.21  % (32524)Time limit reached!
% 6.58/1.21  % (32524)------------------------------
% 6.58/1.21  % (32524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.58/1.21  % (32524)Termination reason: Time limit
% 6.58/1.21  
% 6.58/1.21  % (32524)Memory used [KB]: 6652
% 6.58/1.21  % (32524)Time elapsed: 0.809 s
% 6.58/1.21  % (32524)------------------------------
% 6.58/1.21  % (32524)------------------------------
% 7.41/1.36  % (32549)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 7.96/1.42  % (32505)Time limit reached!
% 7.96/1.42  % (32505)------------------------------
% 7.96/1.42  % (32505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.96/1.42  % (32505)Termination reason: Time limit
% 7.96/1.42  
% 7.96/1.42  % (32505)Memory used [KB]: 17782
% 7.96/1.42  % (32505)Time elapsed: 1.015 s
% 7.96/1.42  % (32505)------------------------------
% 7.96/1.42  % (32505)------------------------------
% 7.96/1.45  % (32540)Refutation found. Thanks to Tanya!
% 7.96/1.45  % SZS status Theorem for theBenchmark
% 7.96/1.45  % SZS output start Proof for theBenchmark
% 7.96/1.45  fof(f7856,plain,(
% 7.96/1.45    $false),
% 7.96/1.45    inference(subsumption_resolution,[],[f7832,f74])).
% 7.96/1.45  fof(f74,plain,(
% 7.96/1.45    r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f42,f37])).
% 7.96/1.45  fof(f37,plain,(
% 7.96/1.45    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 7.96/1.45    inference(cnf_transformation,[],[f27])).
% 7.96/1.45  fof(f27,plain,(
% 7.96/1.45    sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 7.96/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f26])).
% 7.96/1.45  fof(f26,plain,(
% 7.96/1.45    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 7.96/1.45    introduced(choice_axiom,[])).
% 7.96/1.45  fof(f22,plain,(
% 7.96/1.45    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 7.96/1.45    inference(ennf_transformation,[],[f21])).
% 7.96/1.45  fof(f21,negated_conjecture,(
% 7.96/1.45    ~! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 7.96/1.45    inference(negated_conjecture,[],[f20])).
% 7.96/1.45  fof(f20,conjecture,(
% 7.96/1.45    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 7.96/1.45  fof(f42,plain,(
% 7.96/1.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.96/1.45    inference(cnf_transformation,[],[f8])).
% 7.96/1.45  fof(f8,axiom,(
% 7.96/1.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 7.96/1.45  fof(f7832,plain,(
% 7.96/1.45    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f335,f7808])).
% 7.96/1.45  fof(f7808,plain,(
% 7.96/1.45    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f7807,f7165])).
% 7.96/1.45  fof(f7165,plain,(
% 7.96/1.45    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),X10) = X9) )),
% 7.96/1.45    inference(superposition,[],[f6733,f6668])).
% 7.96/1.45  fof(f6668,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6653,f76])).
% 7.96/1.45  fof(f76,plain,(
% 7.96/1.45    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 7.96/1.45    inference(superposition,[],[f44,f40])).
% 7.96/1.45  fof(f40,plain,(
% 7.96/1.45    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.96/1.45    inference(cnf_transformation,[],[f7])).
% 7.96/1.45  fof(f7,axiom,(
% 7.96/1.45    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 7.96/1.45  fof(f44,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.96/1.45    inference(cnf_transformation,[],[f2])).
% 7.96/1.45  fof(f2,axiom,(
% 7.96/1.45    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 7.96/1.45  fof(f6653,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 7.96/1.45    inference(backward_demodulation,[],[f468,f6632])).
% 7.96/1.45  fof(f6632,plain,(
% 7.96/1.45    ( ! [X11] : (k1_xboole_0 = k3_xboole_0(X11,k1_xboole_0)) )),
% 7.96/1.45    inference(backward_demodulation,[],[f674,f6599])).
% 7.96/1.45  fof(f6599,plain,(
% 7.96/1.45    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 7.96/1.45    inference(backward_demodulation,[],[f104,f6563])).
% 7.96/1.45  fof(f6563,plain,(
% 7.96/1.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 7.96/1.45    inference(backward_demodulation,[],[f6245,f6417])).
% 7.96/1.45  fof(f6417,plain,(
% 7.96/1.45    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X2))) )),
% 7.96/1.45    inference(superposition,[],[f118,f6291])).
% 7.96/1.45  fof(f6291,plain,(
% 7.96/1.45    ( ! [X4] : (k3_xboole_0(k1_xboole_0,X4) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6290,f6245])).
% 7.96/1.45  fof(f6290,plain,(
% 7.96/1.45    ( ! [X4] : (k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X4)) = k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6289,f43])).
% 7.96/1.45  fof(f43,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.96/1.45    inference(cnf_transformation,[],[f1])).
% 7.96/1.45  fof(f1,axiom,(
% 7.96/1.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.96/1.45  fof(f6289,plain,(
% 7.96/1.45    ( ! [X4] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) = k3_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0)) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6283,f202])).
% 7.96/1.45  fof(f202,plain,(
% 7.96/1.45    ( ! [X9] : (k3_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X9,X9)) )),
% 7.96/1.45    inference(forward_demodulation,[],[f195,f39])).
% 7.96/1.45  fof(f39,plain,(
% 7.96/1.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.96/1.45    inference(cnf_transformation,[],[f5])).
% 7.96/1.45  fof(f5,axiom,(
% 7.96/1.45    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 7.96/1.45  fof(f195,plain,(
% 7.96/1.45    ( ! [X9] : (k3_xboole_0(X9,k1_xboole_0) = k5_xboole_0(X9,k2_xboole_0(X9,k1_xboole_0))) )),
% 7.96/1.45    inference(superposition,[],[f48,f40])).
% 7.96/1.45  fof(f48,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 7.96/1.45    inference(cnf_transformation,[],[f10])).
% 7.96/1.45  fof(f10,axiom,(
% 7.96/1.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 7.96/1.45  fof(f6283,plain,(
% 7.96/1.45    ( ! [X4] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,X4),k1_xboole_0) = k5_xboole_0(k3_xboole_0(k1_xboole_0,X4),k3_xboole_0(k1_xboole_0,X4))) )),
% 7.96/1.45    inference(superposition,[],[f99,f6245])).
% 7.96/1.45  fof(f99,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 7.96/1.45    inference(superposition,[],[f46,f43])).
% 7.96/1.45  fof(f46,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.96/1.45    inference(cnf_transformation,[],[f4])).
% 7.96/1.45  fof(f4,axiom,(
% 7.96/1.45    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 7.96/1.45  fof(f118,plain,(
% 7.96/1.45    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 7.96/1.45    inference(superposition,[],[f88,f113])).
% 7.96/1.45  fof(f113,plain,(
% 7.96/1.45    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 7.96/1.45    inference(superposition,[],[f47,f76])).
% 7.96/1.45  fof(f47,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.96/1.45    inference(cnf_transformation,[],[f11])).
% 7.96/1.45  fof(f11,axiom,(
% 7.96/1.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 7.96/1.45  fof(f88,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.96/1.45    inference(unit_resulting_resolution,[],[f42,f49])).
% 7.96/1.45  fof(f49,plain,(
% 7.96/1.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 7.96/1.45    inference(cnf_transformation,[],[f23])).
% 7.96/1.45  fof(f23,plain,(
% 7.96/1.45    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.96/1.45    inference(ennf_transformation,[],[f6])).
% 7.96/1.45  fof(f6,axiom,(
% 7.96/1.45    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.96/1.45  fof(f6245,plain,(
% 7.96/1.45    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 7.96/1.45    inference(superposition,[],[f6175,f43])).
% 7.96/1.45  fof(f6175,plain,(
% 7.96/1.45    ( ! [X4] : (k3_xboole_0(k1_xboole_0,X4) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X4,k1_xboole_0))) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6174,f2559])).
% 7.96/1.45  fof(f2559,plain,(
% 7.96/1.45    ( ! [X79] : (k3_xboole_0(k1_xboole_0,X79) = k5_xboole_0(X79,k4_xboole_0(X79,k1_xboole_0))) )),
% 7.96/1.45    inference(forward_demodulation,[],[f2558,f1145])).
% 7.96/1.45  fof(f1145,plain,(
% 7.96/1.45    ( ! [X0] : (k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X0)) = X0) )),
% 7.96/1.45    inference(forward_demodulation,[],[f1140,f76])).
% 7.96/1.45  fof(f1140,plain,(
% 7.96/1.45    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X0))) )),
% 7.96/1.45    inference(superposition,[],[f213,f1044])).
% 7.96/1.45  fof(f1044,plain,(
% 7.96/1.45    k1_xboole_0 = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f1043,f756])).
% 7.96/1.45  fof(f756,plain,(
% 7.96/1.45    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f118,f755])).
% 7.96/1.45  fof(f755,plain,(
% 7.96/1.45    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 7.96/1.45    inference(forward_demodulation,[],[f476,f721])).
% 7.96/1.45  fof(f721,plain,(
% 7.96/1.45    k1_tarski(sK0) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f720,f115])).
% 7.96/1.45  fof(f115,plain,(
% 7.96/1.45    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0) )),
% 7.96/1.45    inference(forward_demodulation,[],[f111,f39])).
% 7.96/1.45  fof(f111,plain,(
% 7.96/1.45    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0))) )),
% 7.96/1.45    inference(superposition,[],[f47,f104])).
% 7.96/1.45  fof(f720,plain,(
% 7.96/1.45    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_xboole_0,k1_tarski(sK0)))),
% 7.96/1.45    inference(superposition,[],[f47,f477])).
% 7.96/1.45  fof(f477,plain,(
% 7.96/1.45    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f463,f43])).
% 7.96/1.45  fof(f463,plain,(
% 7.96/1.45    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 7.96/1.45    inference(backward_demodulation,[],[f103,f202])).
% 7.96/1.45  fof(f103,plain,(
% 7.96/1.45    k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f46,f90])).
% 7.96/1.45  fof(f90,plain,(
% 7.96/1.45    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 7.96/1.45    inference(unit_resulting_resolution,[],[f74,f49])).
% 7.96/1.45  fof(f476,plain,(
% 7.96/1.45    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 7.96/1.45    inference(forward_demodulation,[],[f462,f46])).
% 7.96/1.45  fof(f462,plain,(
% 7.96/1.45    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k1_xboole_0))),
% 7.96/1.45    inference(backward_demodulation,[],[f110,f202])).
% 7.96/1.45  fof(f110,plain,(
% 7.96/1.45    k2_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 7.96/1.45    inference(superposition,[],[f47,f103])).
% 7.96/1.45  fof(f1043,plain,(
% 7.96/1.45    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) = k3_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f1039,f40])).
% 7.96/1.45  fof(f1039,plain,(
% 7.96/1.45    k3_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_xboole_0),k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f190,f759])).
% 7.96/1.45  fof(f759,plain,(
% 7.96/1.45    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f758,f76])).
% 7.96/1.45  fof(f758,plain,(
% 7.96/1.45    k2_xboole_0(k1_xboole_0,k1_tarski(sK0)) = k5_xboole_0(k1_xboole_0,k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f47,f755])).
% 7.96/1.45  fof(f190,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X0,X1))) )),
% 7.96/1.45    inference(superposition,[],[f48,f44])).
% 7.96/1.45  fof(f213,plain,(
% 7.96/1.45    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X1,X0),X2)) )),
% 7.96/1.45    inference(superposition,[],[f54,f44])).
% 7.96/1.45  fof(f54,plain,(
% 7.96/1.45    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 7.96/1.45    inference(cnf_transformation,[],[f9])).
% 7.96/1.45  fof(f9,axiom,(
% 7.96/1.45    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 7.96/1.45  fof(f2558,plain,(
% 7.96/1.45    ( ! [X79] : (k3_xboole_0(k1_xboole_0,X79) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X79)),k4_xboole_0(X79,k1_xboole_0))) )),
% 7.96/1.45    inference(forward_demodulation,[],[f2493,f113])).
% 7.96/1.45  fof(f2493,plain,(
% 7.96/1.45    ( ! [X79] : (k3_xboole_0(k1_xboole_0,X79) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),X79)),k2_xboole_0(k1_xboole_0,X79))) )),
% 7.96/1.45    inference(superposition,[],[f235,f1044])).
% 7.96/1.45  fof(f235,plain,(
% 7.96/1.45    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X2,X3),X4) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X3,X4)),k2_xboole_0(k5_xboole_0(X2,X3),X4))) )),
% 7.96/1.45    inference(superposition,[],[f48,f54])).
% 7.96/1.45  fof(f6174,plain,(
% 7.96/1.45    ( ! [X4] : (k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(X4,k1_xboole_0))) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6173,f43])).
% 7.96/1.45  fof(f6173,plain,(
% 7.96/1.45    ( ! [X4] : (k5_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) = k3_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0)) )),
% 7.96/1.45    inference(forward_demodulation,[],[f5960,f46])).
% 7.96/1.45  fof(f5960,plain,(
% 7.96/1.45    ( ! [X4] : (k3_xboole_0(k3_xboole_0(X4,k1_xboole_0),k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)))) )),
% 7.96/1.45    inference(superposition,[],[f468,f202])).
% 7.96/1.45  fof(f104,plain,(
% 7.96/1.45    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 7.96/1.45    inference(superposition,[],[f46,f76])).
% 7.96/1.45  fof(f674,plain,(
% 7.96/1.45    ( ! [X11] : (k3_xboole_0(X11,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X11)) )),
% 7.96/1.45    inference(superposition,[],[f99,f76])).
% 7.96/1.45  fof(f468,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k3_xboole_0(X0,k1_xboole_0),X1)) )),
% 7.96/1.45    inference(superposition,[],[f54,f202])).
% 7.96/1.45  fof(f6733,plain,(
% 7.96/1.45    ( ! [X14,X13] : (k5_xboole_0(X13,k5_xboole_0(X14,X13)) = X14) )),
% 7.96/1.45    inference(forward_demodulation,[],[f6693,f40])).
% 7.96/1.45  fof(f6693,plain,(
% 7.96/1.45    ( ! [X14,X13] : (k5_xboole_0(X14,k1_xboole_0) = k5_xboole_0(X13,k5_xboole_0(X14,X13))) )),
% 7.96/1.45    inference(superposition,[],[f227,f6652])).
% 7.96/1.45  fof(f6652,plain,(
% 7.96/1.45    ( ! [X9] : (k1_xboole_0 = k5_xboole_0(X9,X9)) )),
% 7.96/1.45    inference(backward_demodulation,[],[f202,f6632])).
% 7.96/1.45  fof(f227,plain,(
% 7.96/1.45    ( ! [X6,X7,X5] : (k5_xboole_0(X7,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k5_xboole_0(X6,X7))) )),
% 7.96/1.45    inference(superposition,[],[f54,f44])).
% 7.96/1.45  fof(f7807,plain,(
% 7.96/1.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK1)) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f7778,f1126])).
% 7.96/1.45  fof(f1126,plain,(
% 7.96/1.45    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 7.96/1.45    inference(forward_demodulation,[],[f1125,f40])).
% 7.96/1.45  fof(f1125,plain,(
% 7.96/1.45    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 7.96/1.45    inference(forward_demodulation,[],[f1124,f756])).
% 7.96/1.45  fof(f1124,plain,(
% 7.96/1.45    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_xboole_0,k1_tarski(sK0)))),
% 7.96/1.45    inference(forward_demodulation,[],[f1123,f43])).
% 7.96/1.45  fof(f1123,plain,(
% 7.96/1.45    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_xboole_0))),
% 7.96/1.45    inference(forward_demodulation,[],[f1090,f202])).
% 7.96/1.45  fof(f1090,plain,(
% 7.96/1.45    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 7.96/1.45    inference(superposition,[],[f213,f199])).
% 7.96/1.45  fof(f199,plain,(
% 7.96/1.45    k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f48,f37])).
% 7.96/1.45  fof(f7778,plain,(
% 7.96/1.45    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) = k2_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 7.96/1.45    inference(superposition,[],[f2284,f7041])).
% 7.96/1.45  fof(f7041,plain,(
% 7.96/1.45    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 7.96/1.45    inference(superposition,[],[f6668,f46])).
% 7.96/1.45  fof(f2284,plain,(
% 7.96/1.45    ( ! [X66] : (k2_xboole_0(k1_tarski(sK1),X66) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(X66,k1_tarski(sK1))))) )),
% 7.96/1.45    inference(superposition,[],[f231,f1386])).
% 7.96/1.45  fof(f1386,plain,(
% 7.96/1.45    k1_tarski(sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))),
% 7.96/1.45    inference(backward_demodulation,[],[f199,f1126])).
% 7.96/1.45  fof(f231,plain,(
% 7.96/1.45    ( ! [X17,X18,X16] : (k2_xboole_0(k5_xboole_0(X16,X17),X18) = k5_xboole_0(X16,k5_xboole_0(X17,k4_xboole_0(X18,k5_xboole_0(X16,X17))))) )),
% 7.96/1.45    inference(superposition,[],[f54,f47])).
% 7.96/1.45  fof(f335,plain,(
% 7.96/1.45    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_tarski(sK1),X0),k1_tarski(sK0))) )),
% 7.96/1.45    inference(unit_resulting_resolution,[],[f137,f322,f50])).
% 7.96/1.45  fof(f50,plain,(
% 7.96/1.45    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 7.96/1.45    inference(cnf_transformation,[],[f31])).
% 7.96/1.45  fof(f31,plain,(
% 7.96/1.45    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.96/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 7.96/1.45  fof(f30,plain,(
% 7.96/1.45    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 7.96/1.45    introduced(choice_axiom,[])).
% 7.96/1.45  fof(f29,plain,(
% 7.96/1.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.96/1.45    inference(rectify,[],[f28])).
% 7.96/1.45  fof(f28,plain,(
% 7.96/1.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.96/1.45    inference(nnf_transformation,[],[f24])).
% 7.96/1.45  fof(f24,plain,(
% 7.96/1.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.96/1.45    inference(ennf_transformation,[],[f3])).
% 7.96/1.45  fof(f3,axiom,(
% 7.96/1.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 7.96/1.45  fof(f322,plain,(
% 7.96/1.45    ~r2_hidden(sK1,k1_tarski(sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f321,f41])).
% 7.96/1.45  fof(f41,plain,(
% 7.96/1.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.96/1.45    inference(cnf_transformation,[],[f13])).
% 7.96/1.45  fof(f13,axiom,(
% 7.96/1.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 7.96/1.45  fof(f321,plain,(
% 7.96/1.45    ~r2_hidden(sK1,k2_tarski(sK0,sK0))),
% 7.96/1.45    inference(forward_demodulation,[],[f305,f45])).
% 7.96/1.45  fof(f45,plain,(
% 7.96/1.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.96/1.45    inference(cnf_transformation,[],[f14])).
% 7.96/1.45  fof(f14,axiom,(
% 7.96/1.45    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 7.96/1.45  fof(f305,plain,(
% 7.96/1.45    ~r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 7.96/1.45    inference(unit_resulting_resolution,[],[f38,f38,f38,f73])).
% 7.96/1.45  fof(f73,plain,(
% 7.96/1.45    ( ! [X2,X0,X5,X1] : (~r2_hidden(X5,k1_enumset1(X0,X1,X2)) | X1 = X5 | X0 = X5 | X2 = X5) )),
% 7.96/1.45    inference(equality_resolution,[],[f56])).
% 7.96/1.45  fof(f56,plain,(
% 7.96/1.45    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 7.96/1.45    inference(cnf_transformation,[],[f36])).
% 7.96/1.45  fof(f36,plain,(
% 7.96/1.45    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.96/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 7.96/1.45  fof(f35,plain,(
% 7.96/1.45    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 7.96/1.45    introduced(choice_axiom,[])).
% 7.96/1.45  fof(f34,plain,(
% 7.96/1.45    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.96/1.45    inference(rectify,[],[f33])).
% 7.96/1.45  fof(f33,plain,(
% 7.96/1.45    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.96/1.45    inference(flattening,[],[f32])).
% 7.96/1.45  fof(f32,plain,(
% 7.96/1.45    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.96/1.45    inference(nnf_transformation,[],[f25])).
% 7.96/1.45  fof(f25,plain,(
% 7.96/1.45    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.96/1.45    inference(ennf_transformation,[],[f12])).
% 7.96/1.45  fof(f12,axiom,(
% 7.96/1.45    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.96/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 7.96/1.45  fof(f38,plain,(
% 7.96/1.45    sK0 != sK1),
% 7.96/1.45    inference(cnf_transformation,[],[f27])).
% 7.96/1.45  fof(f137,plain,(
% 7.96/1.45    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(k1_tarski(X0),X1))) )),
% 7.96/1.45    inference(unit_resulting_resolution,[],[f42,f87,f50])).
% 7.96/1.45  fof(f87,plain,(
% 7.96/1.45    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 7.96/1.45    inference(superposition,[],[f84,f41])).
% 7.96/1.45  fof(f84,plain,(
% 7.96/1.45    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 7.96/1.45    inference(superposition,[],[f72,f45])).
% 7.96/1.45  fof(f72,plain,(
% 7.96/1.45    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 7.96/1.45    inference(equality_resolution,[],[f71])).
% 7.96/1.45  fof(f71,plain,(
% 7.96/1.45    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 7.96/1.45    inference(equality_resolution,[],[f57])).
% 7.96/1.45  fof(f57,plain,(
% 7.96/1.45    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.96/1.45    inference(cnf_transformation,[],[f36])).
% 7.96/1.45  % SZS output end Proof for theBenchmark
% 7.96/1.45  % (32540)------------------------------
% 7.96/1.45  % (32540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.96/1.45  % (32540)Termination reason: Refutation
% 7.96/1.47  
% 7.96/1.47  % (32540)Memory used [KB]: 7036
% 7.96/1.47  % (32540)Time elapsed: 0.597 s
% 7.96/1.47  % (32540)------------------------------
% 7.96/1.47  % (32540)------------------------------
% 8.69/1.47  % (32502)Success in time 1.103 s
%------------------------------------------------------------------------------
