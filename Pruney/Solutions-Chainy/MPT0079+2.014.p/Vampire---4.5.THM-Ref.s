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
% DateTime   : Thu Dec  3 12:30:53 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  139 (2310 expanded)
%              Number of leaves         :   11 ( 684 expanded)
%              Depth                    :   33
%              Number of atoms          :  154 (3744 expanded)
%              Number of equality atoms :  140 (2607 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1733,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1731])).

fof(f1731,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f21,f1663])).

fof(f1663,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1651,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f1651,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f802,f1649])).

fof(f1649,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1634,f599])).

fof(f599,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,sK1)) ),
    inference(backward_demodulation,[],[f544,f591])).

fof(f591,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f590,f31])).

fof(f590,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f589,f65])).

fof(f65,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f42,f39])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f23,f33])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f20,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f589,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f588,f409])).

fof(f409,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f408,f184])).

fof(f184,plain,(
    sK3 = k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f77,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f77,plain,(
    sK3 = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f76,f69])).

fof(f69,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f37,f42])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f76,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(forward_demodulation,[],[f72,f27])).

fof(f72,plain,(
    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[],[f26,f42])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f408,plain,(
    k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f402,f27])).

fof(f402,plain,(
    k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f26,f186])).

fof(f186,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3) ),
    inference(superposition,[],[f29,f77])).

fof(f29,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f588,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK3)) ),
    inference(forward_demodulation,[],[f587,f27])).

fof(f587,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK1,k2_xboole_0(sK3,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f571,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f571,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f39,f393])).

fof(f393,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(superposition,[],[f29,f153])).

fof(f153,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f152,f145])).

fof(f145,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f37,f65])).

fof(f152,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) ),
    inference(forward_demodulation,[],[f148,f27])).

fof(f148,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f26,f65])).

fof(f544,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,k4_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f267,f27])).

fof(f267,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(backward_demodulation,[],[f147,f261])).

fof(f261,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f255,f29])).

fof(f255,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f24,f249])).

fof(f249,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f29,f122])).

fof(f122,plain,(
    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f60,f27])).

fof(f60,plain,(
    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f59,f52])).

fof(f52,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f37,f40])).

fof(f40,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f19,f35])).

fof(f19,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f59,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f55,f27])).

fof(f55,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f26,f40])).

fof(f147,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(superposition,[],[f24,f65])).

fof(f1634,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1358,f1434])).

fof(f1434,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f1339,f27])).

fof(f1339,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f18,f1338])).

fof(f1338,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f1337,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f1337,plain,(
    sK3 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1330,f1157])).

fof(f1157,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1156,f409])).

fof(f1156,plain,(
    k2_xboole_0(k1_xboole_0,sK3) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1155,f27])).

fof(f1155,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1151,f27])).

fof(f1151,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f26,f1145])).

fof(f1145,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f1135,f29])).

fof(f1135,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f529,f18])).

fof(f529,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f24,f509])).

fof(f509,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f508,f31])).

fof(f508,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f507,f48])).

fof(f48,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f40,f39])).

fof(f507,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f506,f318])).

fof(f318,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f317,f122])).

fof(f317,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f311,f27])).

fof(f311,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f26,f124])).

fof(f124,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(superposition,[],[f29,f60])).

fof(f506,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2)) ),
    inference(forward_demodulation,[],[f505,f27])).

fof(f505,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f489,f24])).

fof(f489,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f39,f246])).

fof(f246,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(superposition,[],[f29,f104])).

fof(f104,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f103,f96])).

fof(f96,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f37,f48])).

fof(f103,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f99,f27])).

fof(f99,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0) ),
    inference(superposition,[],[f26,f48])).

fof(f1330,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f26,f1306])).

fof(f1306,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f922,f461])).

fof(f461,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f430,f18])).

fof(f430,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X1,sK3)) ),
    inference(backward_demodulation,[],[f348,f423])).

fof(f423,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f422,f409])).

fof(f422,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f420,f27])).

fof(f420,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(backward_demodulation,[],[f414,f419])).

fof(f419,plain,(
    sK3 = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f418,f31])).

fof(f418,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f417,f65])).

fof(f417,plain,(
    k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) = k4_xboole_0(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f416,f39])).

fof(f416,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f415,f27])).

fof(f415,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k4_xboole_0(sK3,k2_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f405,f24])).

fof(f405,plain,(
    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0) ),
    inference(superposition,[],[f39,f186])).

fof(f414,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f413,f27])).

fof(f413,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK1,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f404,f24])).

fof(f404,plain,(
    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f37,f186])).

fof(f348,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X1,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f263,f27])).

fof(f263,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) ),
    inference(backward_demodulation,[],[f71,f261])).

fof(f71,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0)) ),
    inference(superposition,[],[f24,f42])).

fof(f922,plain,(
    ! [X1] : k4_xboole_0(sK3,X1) = k4_xboole_0(sK3,k2_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f448,f27])).

fof(f448,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f24,f423])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f1358,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f610,f1338])).

fof(f610,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f24,f591])).

fof(f802,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f791,f31])).

fof(f791,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f39,f741])).

fof(f741,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f368,f46])).

fof(f46,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f29,f18])).

fof(f368,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f24,f332])).

fof(f332,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f331,f318])).

fof(f331,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f329,f27])).

fof(f329,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(backward_demodulation,[],[f323,f328])).

fof(f328,plain,(
    sK2 = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f327,f31])).

fof(f327,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f326,f48])).

fof(f326,plain,(
    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(forward_demodulation,[],[f325,f39])).

fof(f325,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f324,f27])).

fof(f324,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f314,f24])).

fof(f314,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) = k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f39,f124])).

fof(f323,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f322,f27])).

fof(f322,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f313,f24])).

fof(f313,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f37,f124])).

fof(f21,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 10:36:16 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (25320)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (25312)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (25314)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (25326)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (25310)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (25330)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (25309)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (25337)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (25311)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (25321)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (25317)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (25308)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (25307)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (25313)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (25319)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (25334)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (25324)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (25335)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (25324)Refutation not found, incomplete strategy% (25324)------------------------------
% 0.22/0.55  % (25324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (25324)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (25324)Memory used [KB]: 10618
% 0.22/0.55  % (25324)Time elapsed: 0.136 s
% 0.22/0.55  % (25324)------------------------------
% 0.22/0.55  % (25324)------------------------------
% 0.22/0.55  % (25327)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (25315)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (25332)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (25336)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (25318)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (25331)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (25333)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (25328)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.57  % (25329)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (25325)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.57  % (25322)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.58  % (25316)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.20/0.65  % (25333)Refutation found. Thanks to Tanya!
% 2.20/0.65  % SZS status Theorem for theBenchmark
% 2.20/0.65  % SZS output start Proof for theBenchmark
% 2.20/0.65  fof(f1733,plain,(
% 2.20/0.65    $false),
% 2.20/0.65    inference(trivial_inequality_removal,[],[f1731])).
% 2.20/0.65  fof(f1731,plain,(
% 2.20/0.65    sK1 != sK1),
% 2.20/0.65    inference(superposition,[],[f21,f1663])).
% 2.20/0.65  fof(f1663,plain,(
% 2.20/0.65    sK1 = sK2),
% 2.20/0.65    inference(forward_demodulation,[],[f1651,f31])).
% 2.20/0.65  fof(f31,plain,(
% 2.20/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.20/0.65    inference(cnf_transformation,[],[f8])).
% 2.20/0.65  fof(f8,axiom,(
% 2.20/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.20/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.20/0.65  fof(f1651,plain,(
% 2.20/0.65    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 2.20/0.65    inference(backward_demodulation,[],[f802,f1649])).
% 2.20/0.65  fof(f1649,plain,(
% 2.20/0.65    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.20/0.65    inference(forward_demodulation,[],[f1634,f599])).
% 2.20/0.65  fof(f599,plain,(
% 2.20/0.65    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,sK1))) )),
% 2.20/0.65    inference(backward_demodulation,[],[f544,f591])).
% 2.20/0.65  fof(f591,plain,(
% 2.20/0.65    sK1 = k4_xboole_0(sK1,sK3)),
% 2.20/0.65    inference(forward_demodulation,[],[f590,f31])).
% 2.20/0.65  fof(f590,plain,(
% 2.20/0.65    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.20/0.65    inference(forward_demodulation,[],[f589,f65])).
% 2.20/0.65  fof(f65,plain,(
% 2.20/0.65    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.20/0.65    inference(superposition,[],[f42,f39])).
% 2.20/0.65  fof(f39,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.20/0.65    inference(definition_unfolding,[],[f34,f33,f33])).
% 2.20/0.65  fof(f33,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f11])).
% 2.20/0.65  fof(f11,axiom,(
% 2.20/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.20/0.65  fof(f34,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f2])).
% 2.20/0.65  fof(f2,axiom,(
% 2.20/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.20/0.65  fof(f42,plain,(
% 2.20/0.65    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.20/0.65    inference(unit_resulting_resolution,[],[f20,f35])).
% 2.20/0.65  fof(f35,plain,(
% 2.20/0.65    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(definition_unfolding,[],[f23,f33])).
% 2.20/0.65  fof(f23,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f3])).
% 2.20/0.65  fof(f3,axiom,(
% 2.20/0.65    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.20/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.20/0.65  fof(f20,plain,(
% 2.20/0.65    r1_xboole_0(sK3,sK1)),
% 2.20/0.65    inference(cnf_transformation,[],[f16])).
% 2.20/0.65  fof(f16,plain,(
% 2.20/0.65    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.20/0.65    inference(flattening,[],[f15])).
% 2.20/0.65  fof(f15,plain,(
% 2.20/0.65    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.20/0.65    inference(ennf_transformation,[],[f14])).
% 2.20/0.65  fof(f14,negated_conjecture,(
% 2.20/0.65    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.20/0.65    inference(negated_conjecture,[],[f13])).
% 2.20/0.68  fof(f13,conjecture,(
% 2.20/0.68    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.20/0.68  fof(f589,plain,(
% 2.20/0.68    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 2.20/0.68    inference(forward_demodulation,[],[f588,f409])).
% 2.20/0.68  fof(f409,plain,(
% 2.20/0.68    sK3 = k2_xboole_0(k1_xboole_0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f408,f184])).
% 2.20/0.68  fof(f184,plain,(
% 2.20/0.68    sK3 = k2_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 2.20/0.68    inference(superposition,[],[f77,f27])).
% 2.20/0.68  fof(f27,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f1])).
% 2.20/0.68  fof(f1,axiom,(
% 2.20/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.20/0.68  fof(f77,plain,(
% 2.20/0.68    sK3 = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f76,f69])).
% 2.20/0.68  fof(f69,plain,(
% 2.20/0.68    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 2.20/0.68    inference(superposition,[],[f37,f42])).
% 2.20/0.68  fof(f37,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.20/0.68    inference(definition_unfolding,[],[f28,f33])).
% 2.20/0.68  fof(f28,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.20/0.68    inference(cnf_transformation,[],[f12])).
% 2.20/0.68  fof(f12,axiom,(
% 2.20/0.68    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.20/0.68  fof(f76,plain,(
% 2.20/0.68    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f72,f27])).
% 2.20/0.68  fof(f72,plain,(
% 2.20/0.68    k2_xboole_0(k4_xboole_0(sK3,sK1),sK3) = k2_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f26,f42])).
% 2.20/0.68  fof(f26,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.20/0.68    inference(cnf_transformation,[],[f7])).
% 2.20/0.68  fof(f7,axiom,(
% 2.20/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.20/0.68  fof(f408,plain,(
% 2.20/0.68    k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k2_xboole_0(k1_xboole_0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f402,f27])).
% 2.20/0.68  fof(f402,plain,(
% 2.20/0.68    k2_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = k2_xboole_0(sK3,k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f26,f186])).
% 2.20/0.68  fof(f186,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK3,sK1),sK3)),
% 2.20/0.68    inference(superposition,[],[f29,f77])).
% 2.20/0.68  fof(f29,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.20/0.68    inference(cnf_transformation,[],[f10])).
% 2.20/0.68  fof(f10,axiom,(
% 2.20/0.68    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.20/0.68  fof(f588,plain,(
% 2.20/0.68    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK1,k2_xboole_0(k1_xboole_0,sK3))),
% 2.20/0.68    inference(forward_demodulation,[],[f587,f27])).
% 2.20/0.68  fof(f587,plain,(
% 2.20/0.68    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(sK1,k2_xboole_0(sK3,k1_xboole_0))),
% 2.20/0.68    inference(forward_demodulation,[],[f571,f24])).
% 2.20/0.68  fof(f24,plain,(
% 2.20/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.20/0.68    inference(cnf_transformation,[],[f9])).
% 2.20/0.68  fof(f9,axiom,(
% 2.20/0.68    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.20/0.68  fof(f571,plain,(
% 2.20/0.68    k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f39,f393])).
% 2.20/0.68  fof(f393,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 2.20/0.68    inference(superposition,[],[f29,f153])).
% 2.20/0.68  fof(f153,plain,(
% 2.20/0.68    sK1 = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 2.20/0.68    inference(forward_demodulation,[],[f152,f145])).
% 2.20/0.68  fof(f145,plain,(
% 2.20/0.68    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 2.20/0.68    inference(superposition,[],[f37,f65])).
% 2.20/0.68  fof(f152,plain,(
% 2.20/0.68    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK1)),
% 2.20/0.68    inference(forward_demodulation,[],[f148,f27])).
% 2.20/0.68  fof(f148,plain,(
% 2.20/0.68    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f26,f65])).
% 2.20/0.68  fof(f544,plain,(
% 2.20/0.68    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X1,k4_xboole_0(sK1,sK3)))) )),
% 2.20/0.68    inference(superposition,[],[f267,f27])).
% 2.20/0.68  fof(f267,plain,(
% 2.20/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 2.20/0.68    inference(backward_demodulation,[],[f147,f261])).
% 2.20/0.68  fof(f261,plain,(
% 2.20/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.20/0.68    inference(forward_demodulation,[],[f255,f29])).
% 2.20/0.68  fof(f255,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))) )),
% 2.20/0.68    inference(superposition,[],[f24,f249])).
% 2.20/0.68  fof(f249,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 2.20/0.68    inference(superposition,[],[f29,f122])).
% 2.20/0.68  fof(f122,plain,(
% 2.20/0.68    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.20/0.68    inference(superposition,[],[f60,f27])).
% 2.20/0.68  fof(f60,plain,(
% 2.20/0.68    sK2 = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f59,f52])).
% 2.20/0.68  fof(f52,plain,(
% 2.20/0.68    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 2.20/0.68    inference(superposition,[],[f37,f40])).
% 2.20/0.68  fof(f40,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.20/0.68    inference(unit_resulting_resolution,[],[f19,f35])).
% 2.20/0.68  fof(f19,plain,(
% 2.20/0.68    r1_xboole_0(sK2,sK0)),
% 2.20/0.68    inference(cnf_transformation,[],[f16])).
% 2.20/0.68  fof(f59,plain,(
% 2.20/0.68    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f55,f27])).
% 2.20/0.68  fof(f55,plain,(
% 2.20/0.68    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f26,f40])).
% 2.20/0.68  fof(f147,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 2.20/0.68    inference(superposition,[],[f24,f65])).
% 2.20/0.68  fof(f1634,plain,(
% 2.20/0.68    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 2.20/0.68    inference(superposition,[],[f1358,f1434])).
% 2.20/0.68  fof(f1434,plain,(
% 2.20/0.68    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 2.20/0.68    inference(superposition,[],[f1339,f27])).
% 2.20/0.68  fof(f1339,plain,(
% 2.20/0.68    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK0)),
% 2.20/0.68    inference(backward_demodulation,[],[f18,f1338])).
% 2.20/0.68  fof(f1338,plain,(
% 2.20/0.68    sK0 = sK3),
% 2.20/0.68    inference(forward_demodulation,[],[f1337,f30])).
% 2.20/0.68  fof(f30,plain,(
% 2.20/0.68    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.20/0.68    inference(cnf_transformation,[],[f4])).
% 2.20/0.68  fof(f4,axiom,(
% 2.20/0.68    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.20/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.20/0.68  fof(f1337,plain,(
% 2.20/0.68    sK3 = k2_xboole_0(sK0,k1_xboole_0)),
% 2.20/0.68    inference(forward_demodulation,[],[f1330,f1157])).
% 2.20/0.68  fof(f1157,plain,(
% 2.20/0.68    sK3 = k2_xboole_0(sK0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f1156,f409])).
% 2.20/0.68  fof(f1156,plain,(
% 2.20/0.68    k2_xboole_0(k1_xboole_0,sK3) = k2_xboole_0(sK0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f1155,f27])).
% 2.20/0.68  fof(f1155,plain,(
% 2.20/0.68    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f1151,f27])).
% 2.20/0.68  fof(f1151,plain,(
% 2.20/0.68    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0)),
% 2.20/0.68    inference(superposition,[],[f26,f1145])).
% 2.20/0.68  fof(f1145,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f1135,f29])).
% 2.20/0.68  fof(f1135,plain,(
% 2.20/0.68    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK3)),
% 2.20/0.68    inference(superposition,[],[f529,f18])).
% 2.20/0.68  fof(f529,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 2.20/0.68    inference(superposition,[],[f24,f509])).
% 2.20/0.68  fof(f509,plain,(
% 2.20/0.68    sK0 = k4_xboole_0(sK0,sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f508,f31])).
% 2.20/0.68  fof(f508,plain,(
% 2.20/0.68    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 2.20/0.68    inference(forward_demodulation,[],[f507,f48])).
% 2.20/0.68  fof(f48,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.20/0.68    inference(superposition,[],[f40,f39])).
% 2.20/0.68  fof(f507,plain,(
% 2.20/0.68    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.20/0.68    inference(forward_demodulation,[],[f506,f318])).
% 2.20/0.68  fof(f318,plain,(
% 2.20/0.68    sK2 = k2_xboole_0(k1_xboole_0,sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f317,f122])).
% 2.20/0.68  fof(f317,plain,(
% 2.20/0.68    k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k2_xboole_0(k1_xboole_0,sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f311,f27])).
% 2.20/0.68  fof(f311,plain,(
% 2.20/0.68    k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k2_xboole_0(sK2,k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f26,f124])).
% 2.20/0.68  fof(f124,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 2.20/0.68    inference(superposition,[],[f29,f60])).
% 2.20/0.68  fof(f506,plain,(
% 2.20/0.68    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,sK2))),
% 2.20/0.68    inference(forward_demodulation,[],[f505,f27])).
% 2.20/0.68  fof(f505,plain,(
% 2.20/0.68    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(sK0,k2_xboole_0(sK2,k1_xboole_0))),
% 2.20/0.68    inference(forward_demodulation,[],[f489,f24])).
% 2.20/0.68  fof(f489,plain,(
% 2.20/0.68    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) = k4_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f39,f246])).
% 2.20/0.68  fof(f246,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 2.20/0.68    inference(superposition,[],[f29,f104])).
% 2.20/0.68  fof(f104,plain,(
% 2.20/0.68    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 2.20/0.68    inference(forward_demodulation,[],[f103,f96])).
% 2.20/0.68  fof(f96,plain,(
% 2.20/0.68    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 2.20/0.68    inference(superposition,[],[f37,f48])).
% 2.20/0.68  fof(f103,plain,(
% 2.20/0.68    k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK2),sK0)),
% 2.20/0.68    inference(forward_demodulation,[],[f99,f27])).
% 2.20/0.68  fof(f99,plain,(
% 2.20/0.68    k2_xboole_0(k4_xboole_0(sK0,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK0,sK2),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f26,f48])).
% 2.20/0.68  fof(f1330,plain,(
% 2.20/0.68    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 2.20/0.68    inference(superposition,[],[f26,f1306])).
% 2.20/0.68  fof(f1306,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 2.20/0.68    inference(superposition,[],[f922,f461])).
% 2.20/0.68  fof(f461,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.20/0.68    inference(superposition,[],[f430,f18])).
% 2.20/0.68  fof(f430,plain,(
% 2.20/0.68    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X1,sK3))) )),
% 2.20/0.68    inference(backward_demodulation,[],[f348,f423])).
% 2.20/0.68  fof(f423,plain,(
% 2.20/0.68    sK3 = k4_xboole_0(sK3,sK1)),
% 2.20/0.68    inference(forward_demodulation,[],[f422,f409])).
% 2.20/0.68  fof(f422,plain,(
% 2.20/0.68    k4_xboole_0(sK3,sK1) = k2_xboole_0(k1_xboole_0,sK3)),
% 2.20/0.68    inference(forward_demodulation,[],[f420,f27])).
% 2.20/0.68  fof(f420,plain,(
% 2.20/0.68    k4_xboole_0(sK3,sK1) = k2_xboole_0(sK3,k1_xboole_0)),
% 2.20/0.68    inference(backward_demodulation,[],[f414,f419])).
% 2.20/0.68  fof(f419,plain,(
% 2.20/0.68    sK3 = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1))),
% 2.20/0.68    inference(forward_demodulation,[],[f418,f31])).
% 2.20/0.68  fof(f418,plain,(
% 2.20/0.68    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1))),
% 2.20/0.68    inference(forward_demodulation,[],[f417,f65])).
% 2.20/0.68  fof(f417,plain,(
% 2.20/0.68    k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)) = k4_xboole_0(sK3,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 2.20/0.68    inference(forward_demodulation,[],[f416,f39])).
% 2.20/0.68  fof(f416,plain,(
% 2.20/0.68    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1))),
% 2.20/0.68    inference(forward_demodulation,[],[f415,f27])).
% 2.20/0.68  fof(f415,plain,(
% 2.20/0.68    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k4_xboole_0(sK3,k2_xboole_0(sK1,k1_xboole_0))),
% 2.20/0.68    inference(forward_demodulation,[],[f405,f24])).
% 2.20/0.68  fof(f405,plain,(
% 2.20/0.68    k4_xboole_0(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f39,f186])).
% 2.20/0.68  fof(f414,plain,(
% 2.20/0.68    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(k1_xboole_0,sK1)),k1_xboole_0)),
% 2.20/0.68    inference(forward_demodulation,[],[f413,f27])).
% 2.20/0.68  fof(f413,plain,(
% 2.20/0.68    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(sK3,k2_xboole_0(sK1,k1_xboole_0)),k1_xboole_0)),
% 2.20/0.68    inference(forward_demodulation,[],[f404,f24])).
% 2.20/0.68  fof(f404,plain,(
% 2.20/0.68    k4_xboole_0(sK3,sK1) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK3,sK1),k1_xboole_0),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f37,f186])).
% 2.20/0.68  fof(f348,plain,(
% 2.20/0.68    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(X1,k4_xboole_0(sK3,sK1)))) )),
% 2.20/0.68    inference(superposition,[],[f263,f27])).
% 2.20/0.68  fof(f263,plain,(
% 2.20/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0))) )),
% 2.20/0.68    inference(backward_demodulation,[],[f71,f261])).
% 2.20/0.68  fof(f71,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(k4_xboole_0(sK3,sK1),X0))) )),
% 2.20/0.68    inference(superposition,[],[f24,f42])).
% 2.20/0.68  fof(f922,plain,(
% 2.20/0.68    ( ! [X1] : (k4_xboole_0(sK3,X1) = k4_xboole_0(sK3,k2_xboole_0(X1,sK1))) )),
% 2.20/0.68    inference(superposition,[],[f448,f27])).
% 2.20/0.68  fof(f448,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 2.20/0.68    inference(superposition,[],[f24,f423])).
% 2.20/0.68  fof(f18,plain,(
% 2.20/0.68    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.20/0.68    inference(cnf_transformation,[],[f16])).
% 2.20/0.68  fof(f1358,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0))) )),
% 2.20/0.68    inference(backward_demodulation,[],[f610,f1338])).
% 2.20/0.68  fof(f610,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 2.20/0.68    inference(superposition,[],[f24,f591])).
% 2.20/0.68  fof(f802,plain,(
% 2.20/0.68    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.20/0.68    inference(forward_demodulation,[],[f791,f31])).
% 2.20/0.68  fof(f791,plain,(
% 2.20/0.68    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.20/0.68    inference(superposition,[],[f39,f741])).
% 2.20/0.68  fof(f741,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 2.20/0.68    inference(superposition,[],[f368,f46])).
% 2.20/0.68  fof(f46,plain,(
% 2.20/0.68    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.20/0.68    inference(superposition,[],[f29,f18])).
% 2.20/0.68  fof(f368,plain,(
% 2.20/0.68    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 2.20/0.68    inference(superposition,[],[f24,f332])).
% 2.20/0.68  fof(f332,plain,(
% 2.20/0.68    sK2 = k4_xboole_0(sK2,sK0)),
% 2.20/0.68    inference(forward_demodulation,[],[f331,f318])).
% 2.20/0.68  fof(f331,plain,(
% 2.20/0.68    k4_xboole_0(sK2,sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 2.20/0.68    inference(forward_demodulation,[],[f329,f27])).
% 2.20/0.68  fof(f329,plain,(
% 2.20/0.68    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k1_xboole_0)),
% 2.20/0.68    inference(backward_demodulation,[],[f323,f328])).
% 2.20/0.68  fof(f328,plain,(
% 2.20/0.68    sK2 = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))),
% 2.20/0.68    inference(forward_demodulation,[],[f327,f31])).
% 2.20/0.68  fof(f327,plain,(
% 2.20/0.68    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))),
% 2.20/0.68    inference(forward_demodulation,[],[f326,f48])).
% 2.20/0.68  fof(f326,plain,(
% 2.20/0.68    k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)) = k4_xboole_0(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 2.20/0.68    inference(forward_demodulation,[],[f325,f39])).
% 2.20/0.68  fof(f325,plain,(
% 2.20/0.68    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0))),
% 2.20/0.68    inference(forward_demodulation,[],[f324,f27])).
% 2.20/0.68  fof(f324,plain,(
% 2.20/0.68    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) = k4_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0))),
% 2.20/0.68    inference(forward_demodulation,[],[f314,f24])).
% 2.20/0.68  fof(f314,plain,(
% 2.20/0.68    k4_xboole_0(sK2,k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))) = k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f39,f124])).
% 2.20/0.68  fof(f323,plain,(
% 2.20/0.68    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(k1_xboole_0,sK0)),k1_xboole_0)),
% 2.20/0.68    inference(forward_demodulation,[],[f322,f27])).
% 2.20/0.68  fof(f322,plain,(
% 2.20/0.68    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK0,k1_xboole_0)),k1_xboole_0)),
% 2.20/0.68    inference(forward_demodulation,[],[f313,f24])).
% 2.20/0.68  fof(f313,plain,(
% 2.20/0.68    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0),k1_xboole_0)),
% 2.20/0.68    inference(superposition,[],[f37,f124])).
% 2.20/0.68  fof(f21,plain,(
% 2.20/0.68    sK1 != sK2),
% 2.20/0.68    inference(cnf_transformation,[],[f16])).
% 2.20/0.68  % SZS output end Proof for theBenchmark
% 2.20/0.68  % (25333)------------------------------
% 2.20/0.68  % (25333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (25333)Termination reason: Refutation
% 2.20/0.68  
% 2.20/0.68  % (25333)Memory used [KB]: 7036
% 2.20/0.68  % (25333)Time elapsed: 0.244 s
% 2.20/0.68  % (25333)------------------------------
% 2.20/0.68  % (25333)------------------------------
% 2.20/0.68  % (25298)Success in time 0.312 s
%------------------------------------------------------------------------------
