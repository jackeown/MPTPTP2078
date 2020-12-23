%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:32 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  102 (2405 expanded)
%              Number of leaves         :   11 ( 825 expanded)
%              Depth                    :   35
%              Number of atoms          :  118 (2432 expanded)
%              Number of equality atoms :   92 (2391 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7372,f17])).

fof(f17,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f7372,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f7245,f6841])).

fof(f6841,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f541,f6529])).

fof(f6529,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),X10) ),
    inference(forward_demodulation,[],[f6528,f6412])).

fof(f6412,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k4_xboole_0(X96,X95) ),
    inference(forward_demodulation,[],[f6411,f239])).

fof(f239,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = X19 ),
    inference(forward_demodulation,[],[f238,f20])).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f238,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = k4_xboole_0(X19,k1_xboole_0) ),
    inference(forward_demodulation,[],[f237,f74])).

fof(f74,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f63,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f63,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f27,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f28,f20])).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f237,plain,(
    ! [X19] : k2_xboole_0(X19,k1_xboole_0) = k4_xboole_0(X19,k4_xboole_0(X19,k2_xboole_0(X19,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f192,f20])).

fof(f192,plain,(
    ! [X19] : k4_xboole_0(X19,k4_xboole_0(X19,k2_xboole_0(X19,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X19,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f29,f140])).

fof(f140,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X5,k1_xboole_0),X5) ),
    inference(superposition,[],[f67,f33])).

fof(f67,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    inference(superposition,[],[f27,f20])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f21,f22,f22])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6411,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k4_xboole_0(X96,k2_xboole_0(X95,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f6410,f224])).

fof(f224,plain,(
    ! [X18] : k2_xboole_0(k1_xboole_0,X18) = X18 ),
    inference(forward_demodulation,[],[f223,f20])).

fof(f223,plain,(
    ! [X18] : k2_xboole_0(k1_xboole_0,X18) = k4_xboole_0(X18,k1_xboole_0) ),
    inference(forward_demodulation,[],[f222,f33])).

fof(f222,plain,(
    ! [X18] : k2_xboole_0(k1_xboole_0,X18) = k4_xboole_0(X18,k4_xboole_0(X18,X18)) ),
    inference(forward_demodulation,[],[f221,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f27,f20])).

fof(f221,plain,(
    ! [X18] : k2_xboole_0(k1_xboole_0,X18) = k4_xboole_0(X18,k4_xboole_0(X18,k2_xboole_0(k1_xboole_0,X18))) ),
    inference(forward_demodulation,[],[f191,f20])).

fof(f191,plain,(
    ! [X18] : k4_xboole_0(X18,k4_xboole_0(X18,k2_xboole_0(k1_xboole_0,X18))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k1_xboole_0) ),
    inference(superposition,[],[f29,f108])).

fof(f108,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4) ),
    inference(superposition,[],[f62,f33])).

fof(f6410,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f6409,f2596])).

fof(f2596,plain,(
    ! [X26,X24,X25] : k1_xboole_0 = k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(X26,X24))) ),
    inference(superposition,[],[f77,f79])).

fof(f79,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f68,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f68,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f27,f33])).

fof(f77,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X8),X9)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X8,X9))) ),
    inference(forward_demodulation,[],[f76,f27])).

fof(f76,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X8,X9)) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X8),X9)) ),
    inference(forward_demodulation,[],[f65,f27])).

fof(f65,plain,(
    ! [X6,X8,X7,X9] : k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X8,X9)) = k4_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X8)),X9) ),
    inference(superposition,[],[f27,f27])).

fof(f6409,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(X96,k2_xboole_0(X95,k2_xboole_0(X95,X96)))))) ),
    inference(forward_demodulation,[],[f6408,f24])).

fof(f6408,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(k2_xboole_0(X95,X96),X95)))))) ),
    inference(forward_demodulation,[],[f6407,f27])).

fof(f6407,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(k4_xboole_0(X96,X95),k4_xboole_0(k2_xboole_0(X95,X96),X95))))) ),
    inference(forward_demodulation,[],[f6224,f27])).

fof(f6224,plain,(
    ! [X95,X96] : k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X96,X95),k4_xboole_0(k4_xboole_0(X96,X95),k4_xboole_0(k2_xboole_0(X95,X96),X95)))) ),
    inference(superposition,[],[f5625,f1425])).

fof(f1425,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f1393,f24])).

fof(f1393,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X8),X9),X8) ),
    inference(superposition,[],[f79,f1354])).

fof(f1354,plain,(
    ! [X17,X18] : k2_xboole_0(X18,k4_xboole_0(k2_xboole_0(X17,X18),X17)) = X18 ),
    inference(forward_demodulation,[],[f1320,f239])).

fof(f1320,plain,(
    ! [X17,X18] : k2_xboole_0(X18,k1_xboole_0) = k2_xboole_0(X18,k4_xboole_0(k2_xboole_0(X17,X18),X17)) ),
    inference(superposition,[],[f71,f33])).

fof(f71,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f24,f27])).

fof(f5625,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8 ),
    inference(backward_demodulation,[],[f210,f5624])).

fof(f5624,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,X8),X7) = X7 ),
    inference(forward_demodulation,[],[f5623,f20])).

fof(f5623,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(forward_demodulation,[],[f5622,f79])).

fof(f5622,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X7))) ),
    inference(forward_demodulation,[],[f5542,f20])).

fof(f5542,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X7))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X8),X7),k1_xboole_0) ),
    inference(superposition,[],[f29,f5394])).

fof(f5394,plain,(
    ! [X26,X25] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X25,X26),X25),X25) ),
    inference(superposition,[],[f79,f5222])).

fof(f5222,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X3)) = X3 ),
    inference(superposition,[],[f2487,f24])).

fof(f2487,plain,(
    ! [X12,X10,X11] : k2_xboole_0(X12,k4_xboole_0(k2_xboole_0(k4_xboole_0(X10,X11),X12),X10)) = X12 ),
    inference(superposition,[],[f1364,f730])).

fof(f730,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f714,f239])).

fof(f714,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f24,f675])).

fof(f675,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f674,f33])).

fof(f674,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f635,f496])).

fof(f496,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f635,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f496,f29])).

fof(f1364,plain,(
    ! [X30,X31,X32] : k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),k2_xboole_0(X32,X30))) = X31 ),
    inference(forward_demodulation,[],[f1363,f27])).

fof(f1363,plain,(
    ! [X30,X31,X32] : k2_xboole_0(X31,k4_xboole_0(k4_xboole_0(k2_xboole_0(X30,X31),X32),X30)) = X31 ),
    inference(forward_demodulation,[],[f1325,f239])).

fof(f1325,plain,(
    ! [X30,X31,X32] : k2_xboole_0(X31,k4_xboole_0(k4_xboole_0(k2_xboole_0(X30,X31),X32),X30)) = k2_xboole_0(X31,k1_xboole_0) ),
    inference(superposition,[],[f71,f675])).

fof(f210,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X8) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) ),
    inference(superposition,[],[f24,f29])).

fof(f6528,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),X10),X10) ),
    inference(forward_demodulation,[],[f6241,f20])).

fof(f6241,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),X10),k4_xboole_0(X10,k1_xboole_0)) ),
    inference(superposition,[],[f5625,f74])).

fof(f541,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f27,f530])).

fof(f530,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f500,f20])).

fof(f500,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f30,f44])).

fof(f44,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f25,f22])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f7245,plain,(
    ! [X59,X60,X58] : r1_xboole_0(X60,k4_xboole_0(X58,k2_xboole_0(X59,X60))) ),
    inference(superposition,[],[f7209,f27])).

fof(f7209,plain,(
    ! [X26,X27] : r1_xboole_0(X26,k4_xboole_0(X27,X26)) ),
    inference(subsumption_resolution,[],[f7178,f33])).

fof(f7178,plain,(
    ! [X26,X27] :
      ( k1_xboole_0 != k4_xboole_0(X26,X26)
      | r1_xboole_0(X26,k4_xboole_0(X27,X26)) ) ),
    inference(superposition,[],[f31,f7089])).

fof(f7089,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5 ),
    inference(forward_demodulation,[],[f7088,f20])).

fof(f7088,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,k4_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f7087,f74])).

fof(f7087,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) = k4_xboole_0(X5,k4_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f7023,f7013])).

fof(f7013,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X26,X27)) = k4_xboole_0(X27,k4_xboole_0(X26,X27)) ),
    inference(superposition,[],[f6412,f6529])).

fof(f7023,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f29,f6412])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (5283)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.46  % (5277)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (5276)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (5288)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (5275)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.46  % (5285)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (5278)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (5290)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.47  % (5284)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (5274)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (5282)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (5280)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (5281)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (5279)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (5291)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (5286)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (5289)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (5287)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.77/0.62  % (5283)Refutation found. Thanks to Tanya!
% 1.77/0.62  % SZS status Theorem for theBenchmark
% 1.77/0.62  % SZS output start Proof for theBenchmark
% 1.77/0.62  fof(f7375,plain,(
% 1.77/0.62    $false),
% 1.77/0.62    inference(subsumption_resolution,[],[f7372,f17])).
% 1.77/0.62  fof(f17,plain,(
% 1.77/0.62    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.77/0.62    inference(cnf_transformation,[],[f14])).
% 1.77/0.62  fof(f14,plain,(
% 1.77/0.62    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.77/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 1.77/0.62  fof(f13,plain,(
% 1.77/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.77/0.62    introduced(choice_axiom,[])).
% 1.77/0.62  fof(f12,plain,(
% 1.77/0.62    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 1.77/0.62    inference(ennf_transformation,[],[f11])).
% 1.77/0.62  fof(f11,negated_conjecture,(
% 1.77/0.62    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.77/0.62    inference(negated_conjecture,[],[f10])).
% 1.77/0.62  fof(f10,conjecture,(
% 1.77/0.62    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 1.77/0.62  fof(f7372,plain,(
% 1.77/0.62    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 1.77/0.62    inference(superposition,[],[f7245,f6841])).
% 1.77/0.62  fof(f6841,plain,(
% 1.77/0.62    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 1.77/0.62    inference(superposition,[],[f541,f6529])).
% 1.77/0.62  fof(f6529,plain,(
% 1.77/0.62    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(X11,X10),X10)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6528,f6412])).
% 1.77/0.62  fof(f6412,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k4_xboole_0(X96,X95)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6411,f239])).
% 1.77/0.62  fof(f239,plain,(
% 1.77/0.62    ( ! [X19] : (k2_xboole_0(X19,k1_xboole_0) = X19) )),
% 1.77/0.62    inference(forward_demodulation,[],[f238,f20])).
% 1.77/0.62  fof(f20,plain,(
% 1.77/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f5])).
% 1.77/0.62  fof(f5,axiom,(
% 1.77/0.62    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.77/0.62  fof(f238,plain,(
% 1.77/0.62    ( ! [X19] : (k2_xboole_0(X19,k1_xboole_0) = k4_xboole_0(X19,k1_xboole_0)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f237,f74])).
% 1.77/0.62  fof(f74,plain,(
% 1.77/0.62    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f63,f19])).
% 1.77/0.62  fof(f19,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f9])).
% 1.77/0.62  fof(f9,axiom,(
% 1.77/0.62    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 1.77/0.62  fof(f63,plain,(
% 1.77/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.77/0.62    inference(superposition,[],[f27,f33])).
% 1.77/0.62  fof(f33,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.77/0.62    inference(backward_demodulation,[],[f28,f20])).
% 1.77/0.62  fof(f28,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f18,f22])).
% 1.77/0.62  fof(f22,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f8])).
% 1.77/0.62  fof(f8,axiom,(
% 1.77/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.77/0.62  fof(f18,plain,(
% 1.77/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f3])).
% 1.77/0.62  fof(f3,axiom,(
% 1.77/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.77/0.62  fof(f27,plain,(
% 1.77/0.62    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f6])).
% 1.77/0.62  fof(f6,axiom,(
% 1.77/0.62    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.77/0.62  fof(f237,plain,(
% 1.77/0.62    ( ! [X19] : (k2_xboole_0(X19,k1_xboole_0) = k4_xboole_0(X19,k4_xboole_0(X19,k2_xboole_0(X19,k1_xboole_0)))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f192,f20])).
% 1.77/0.62  fof(f192,plain,(
% 1.77/0.62    ( ! [X19] : (k4_xboole_0(X19,k4_xboole_0(X19,k2_xboole_0(X19,k1_xboole_0))) = k4_xboole_0(k2_xboole_0(X19,k1_xboole_0),k1_xboole_0)) )),
% 1.77/0.62    inference(superposition,[],[f29,f140])).
% 1.77/0.62  fof(f140,plain,(
% 1.77/0.62    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X5,k1_xboole_0),X5)) )),
% 1.77/0.62    inference(superposition,[],[f67,f33])).
% 1.77/0.62  fof(f67,plain,(
% 1.77/0.62    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) )),
% 1.77/0.62    inference(superposition,[],[f27,f20])).
% 1.77/0.62  fof(f29,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f21,f22,f22])).
% 1.77/0.62  fof(f21,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f1])).
% 1.77/0.62  fof(f1,axiom,(
% 1.77/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.77/0.62  fof(f6411,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k4_xboole_0(X96,k2_xboole_0(X95,k1_xboole_0))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6410,f224])).
% 1.77/0.62  fof(f224,plain,(
% 1.77/0.62    ( ! [X18] : (k2_xboole_0(k1_xboole_0,X18) = X18) )),
% 1.77/0.62    inference(forward_demodulation,[],[f223,f20])).
% 1.77/0.62  fof(f223,plain,(
% 1.77/0.62    ( ! [X18] : (k2_xboole_0(k1_xboole_0,X18) = k4_xboole_0(X18,k1_xboole_0)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f222,f33])).
% 1.77/0.62  fof(f222,plain,(
% 1.77/0.62    ( ! [X18] : (k2_xboole_0(k1_xboole_0,X18) = k4_xboole_0(X18,k4_xboole_0(X18,X18))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f221,f62])).
% 1.77/0.62  fof(f62,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 1.77/0.62    inference(superposition,[],[f27,f20])).
% 1.77/0.62  fof(f221,plain,(
% 1.77/0.62    ( ! [X18] : (k2_xboole_0(k1_xboole_0,X18) = k4_xboole_0(X18,k4_xboole_0(X18,k2_xboole_0(k1_xboole_0,X18)))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f191,f20])).
% 1.77/0.62  fof(f191,plain,(
% 1.77/0.62    ( ! [X18] : (k4_xboole_0(X18,k4_xboole_0(X18,k2_xboole_0(k1_xboole_0,X18))) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X18),k1_xboole_0)) )),
% 1.77/0.62    inference(superposition,[],[f29,f108])).
% 1.77/0.62  fof(f108,plain,(
% 1.77/0.62    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4)) )),
% 1.77/0.62    inference(superposition,[],[f62,f33])).
% 1.77/0.62  fof(f6410,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k1_xboole_0)))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6409,f2596])).
% 1.77/0.62  fof(f2596,plain,(
% 1.77/0.62    ( ! [X26,X24,X25] : (k1_xboole_0 = k4_xboole_0(X24,k2_xboole_0(X25,k2_xboole_0(X26,X24)))) )),
% 1.77/0.62    inference(superposition,[],[f77,f79])).
% 1.77/0.62  fof(f79,plain,(
% 1.77/0.62    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f68,f24])).
% 1.77/0.62  fof(f24,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f4])).
% 1.77/0.62  fof(f4,axiom,(
% 1.77/0.62    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.77/0.62  fof(f68,plain,(
% 1.77/0.62    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.77/0.62    inference(superposition,[],[f27,f33])).
% 1.77/0.62  fof(f77,plain,(
% 1.77/0.62    ( ! [X6,X8,X7,X9] : (k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X8),X9)) = k4_xboole_0(X6,k2_xboole_0(X7,k2_xboole_0(X8,X9)))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f76,f27])).
% 1.77/0.62  fof(f76,plain,(
% 1.77/0.62    ( ! [X6,X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X8,X9)) = k4_xboole_0(X6,k2_xboole_0(k2_xboole_0(X7,X8),X9))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f65,f27])).
% 1.77/0.62  fof(f65,plain,(
% 1.77/0.62    ( ! [X6,X8,X7,X9] : (k4_xboole_0(k4_xboole_0(X6,X7),k2_xboole_0(X8,X9)) = k4_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X8)),X9)) )),
% 1.77/0.62    inference(superposition,[],[f27,f27])).
% 1.77/0.62  fof(f6409,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(X96,k2_xboole_0(X95,k2_xboole_0(X95,X96))))))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6408,f24])).
% 1.77/0.62  fof(f6408,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(k2_xboole_0(X95,X96),X95))))))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6407,f27])).
% 1.77/0.62  fof(f6407,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X96,k2_xboole_0(X95,k4_xboole_0(k4_xboole_0(X96,X95),k4_xboole_0(k2_xboole_0(X95,X96),X95)))))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6224,f27])).
% 1.77/0.62  fof(f6224,plain,(
% 1.77/0.62    ( ! [X95,X96] : (k4_xboole_0(k2_xboole_0(X95,X96),X95) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X96,X95),k4_xboole_0(k4_xboole_0(X96,X95),k4_xboole_0(k2_xboole_0(X95,X96),X95))))) )),
% 1.77/0.62    inference(superposition,[],[f5625,f1425])).
% 1.77/0.62  fof(f1425,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),k4_xboole_0(X1,X0))) )),
% 1.77/0.62    inference(superposition,[],[f1393,f24])).
% 1.77/0.62  fof(f1393,plain,(
% 1.77/0.62    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X9,X8),X9),X8)) )),
% 1.77/0.62    inference(superposition,[],[f79,f1354])).
% 1.77/0.62  fof(f1354,plain,(
% 1.77/0.62    ( ! [X17,X18] : (k2_xboole_0(X18,k4_xboole_0(k2_xboole_0(X17,X18),X17)) = X18) )),
% 1.77/0.62    inference(forward_demodulation,[],[f1320,f239])).
% 1.77/0.62  fof(f1320,plain,(
% 1.77/0.62    ( ! [X17,X18] : (k2_xboole_0(X18,k1_xboole_0) = k2_xboole_0(X18,k4_xboole_0(k2_xboole_0(X17,X18),X17))) )),
% 1.77/0.62    inference(superposition,[],[f71,f33])).
% 1.77/0.62  fof(f71,plain,(
% 1.77/0.62    ( ! [X6,X7,X5] : (k2_xboole_0(X7,k4_xboole_0(X5,X6)) = k2_xboole_0(X7,k4_xboole_0(X5,k2_xboole_0(X6,X7)))) )),
% 1.77/0.62    inference(superposition,[],[f24,f27])).
% 1.77/0.62  fof(f5625,plain,(
% 1.77/0.62    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8))) = X8) )),
% 1.77/0.62    inference(backward_demodulation,[],[f210,f5624])).
% 1.77/0.62  fof(f5624,plain,(
% 1.77/0.62    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,X8),X7) = X7) )),
% 1.77/0.62    inference(forward_demodulation,[],[f5623,f20])).
% 1.77/0.62  fof(f5623,plain,(
% 1.77/0.62    ( ! [X8,X7] : (k4_xboole_0(X7,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f5622,f79])).
% 1.77/0.62  fof(f5622,plain,(
% 1.77/0.62    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,X8),X7) = k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X7)))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f5542,f20])).
% 1.77/0.62  fof(f5542,plain,(
% 1.77/0.62    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,k2_xboole_0(k4_xboole_0(X7,X8),X7))) = k4_xboole_0(k2_xboole_0(k4_xboole_0(X7,X8),X7),k1_xboole_0)) )),
% 1.77/0.62    inference(superposition,[],[f29,f5394])).
% 1.77/0.62  fof(f5394,plain,(
% 1.77/0.62    ( ! [X26,X25] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X25,X26),X25),X25)) )),
% 1.77/0.62    inference(superposition,[],[f79,f5222])).
% 1.77/0.62  fof(f5222,plain,(
% 1.77/0.62    ( ! [X4,X3] : (k2_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X3)) = X3) )),
% 1.77/0.62    inference(superposition,[],[f2487,f24])).
% 1.77/0.62  fof(f2487,plain,(
% 1.77/0.62    ( ! [X12,X10,X11] : (k2_xboole_0(X12,k4_xboole_0(k2_xboole_0(k4_xboole_0(X10,X11),X12),X10)) = X12) )),
% 1.77/0.62    inference(superposition,[],[f1364,f730])).
% 1.77/0.62  fof(f730,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.77/0.62    inference(forward_demodulation,[],[f714,f239])).
% 1.77/0.62  fof(f714,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(superposition,[],[f24,f675])).
% 1.77/0.62  fof(f675,plain,(
% 1.77/0.62    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,X3),X2)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f674,f33])).
% 1.77/0.62  fof(f674,plain,(
% 1.77/0.62    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f635,f496])).
% 1.77/0.62  fof(f496,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.77/0.62    inference(superposition,[],[f30,f29])).
% 1.77/0.62  fof(f30,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f23,f22])).
% 1.77/0.62  fof(f23,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(cnf_transformation,[],[f7])).
% 1.77/0.62  fof(f7,axiom,(
% 1.77/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.77/0.62  fof(f635,plain,(
% 1.77/0.62    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 1.77/0.62    inference(superposition,[],[f496,f29])).
% 1.77/0.62  fof(f1364,plain,(
% 1.77/0.62    ( ! [X30,X31,X32] : (k2_xboole_0(X31,k4_xboole_0(k2_xboole_0(X30,X31),k2_xboole_0(X32,X30))) = X31) )),
% 1.77/0.62    inference(forward_demodulation,[],[f1363,f27])).
% 1.77/0.62  fof(f1363,plain,(
% 1.77/0.62    ( ! [X30,X31,X32] : (k2_xboole_0(X31,k4_xboole_0(k4_xboole_0(k2_xboole_0(X30,X31),X32),X30)) = X31) )),
% 1.77/0.62    inference(forward_demodulation,[],[f1325,f239])).
% 1.77/0.62  fof(f1325,plain,(
% 1.77/0.62    ( ! [X30,X31,X32] : (k2_xboole_0(X31,k4_xboole_0(k4_xboole_0(k2_xboole_0(X30,X31),X32),X30)) = k2_xboole_0(X31,k1_xboole_0)) )),
% 1.77/0.62    inference(superposition,[],[f71,f675])).
% 1.77/0.62  fof(f210,plain,(
% 1.77/0.62    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X8) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X9,X8)))) )),
% 1.77/0.62    inference(superposition,[],[f24,f29])).
% 1.77/0.62  fof(f6528,plain,(
% 1.77/0.62    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),X10),X10)) )),
% 1.77/0.62    inference(forward_demodulation,[],[f6241,f20])).
% 1.77/0.62  fof(f6241,plain,(
% 1.77/0.62    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X10,X11),X10),k4_xboole_0(X10,k1_xboole_0))) )),
% 1.77/0.62    inference(superposition,[],[f5625,f74])).
% 1.77/0.62  fof(f541,plain,(
% 1.77/0.62    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0)) )),
% 1.77/0.62    inference(superposition,[],[f27,f530])).
% 1.77/0.62  fof(f530,plain,(
% 1.77/0.62    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.77/0.62    inference(forward_demodulation,[],[f500,f20])).
% 1.77/0.62  fof(f500,plain,(
% 1.77/0.62    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.77/0.62    inference(superposition,[],[f30,f44])).
% 1.77/0.62  fof(f44,plain,(
% 1.77/0.62    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 1.77/0.62    inference(resolution,[],[f32,f16])).
% 1.77/0.62  fof(f16,plain,(
% 1.77/0.62    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.77/0.62    inference(cnf_transformation,[],[f14])).
% 1.77/0.62  fof(f32,plain,(
% 1.77/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.77/0.62    inference(definition_unfolding,[],[f25,f22])).
% 1.77/0.62  fof(f25,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.77/0.62    inference(cnf_transformation,[],[f15])).
% 1.77/0.62  fof(f15,plain,(
% 1.77/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.77/0.62    inference(nnf_transformation,[],[f2])).
% 1.77/0.62  fof(f2,axiom,(
% 1.77/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.77/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.77/0.62  fof(f7245,plain,(
% 1.77/0.62    ( ! [X59,X60,X58] : (r1_xboole_0(X60,k4_xboole_0(X58,k2_xboole_0(X59,X60)))) )),
% 1.77/0.62    inference(superposition,[],[f7209,f27])).
% 1.77/0.62  fof(f7209,plain,(
% 1.77/0.62    ( ! [X26,X27] : (r1_xboole_0(X26,k4_xboole_0(X27,X26))) )),
% 1.77/0.62    inference(subsumption_resolution,[],[f7178,f33])).
% 1.77/0.62  fof(f7178,plain,(
% 1.77/0.62    ( ! [X26,X27] : (k1_xboole_0 != k4_xboole_0(X26,X26) | r1_xboole_0(X26,k4_xboole_0(X27,X26))) )),
% 1.77/0.62    inference(superposition,[],[f31,f7089])).
% 1.77/0.62  fof(f7089,plain,(
% 1.77/0.62    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) )),
% 1.77/0.62    inference(forward_demodulation,[],[f7088,f20])).
% 1.77/0.62  fof(f7088,plain,(
% 1.77/0.62    ( ! [X6,X5] : (k4_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,k4_xboole_0(X6,X5))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f7087,f74])).
% 1.77/0.62  fof(f7087,plain,(
% 1.77/0.62    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) = k4_xboole_0(X5,k4_xboole_0(X6,X5))) )),
% 1.77/0.62    inference(forward_demodulation,[],[f7023,f7013])).
% 1.77/0.62  fof(f7013,plain,(
% 1.77/0.62    ( ! [X26,X27] : (k4_xboole_0(k2_xboole_0(X27,X26),k4_xboole_0(X26,X27)) = k4_xboole_0(X27,k4_xboole_0(X26,X27))) )),
% 1.77/0.62    inference(superposition,[],[f6412,f6529])).
% 1.77/0.62  fof(f7023,plain,(
% 1.77/0.62    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,k2_xboole_0(X5,X6))) = k4_xboole_0(k2_xboole_0(X5,X6),k4_xboole_0(X6,X5))) )),
% 1.77/0.62    inference(superposition,[],[f29,f6412])).
% 1.77/0.62  fof(f31,plain,(
% 1.77/0.62    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.77/0.62    inference(definition_unfolding,[],[f26,f22])).
% 1.77/0.62  fof(f26,plain,(
% 1.77/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.77/0.62    inference(cnf_transformation,[],[f15])).
% 1.77/0.62  % SZS output end Proof for theBenchmark
% 1.77/0.62  % (5283)------------------------------
% 1.77/0.62  % (5283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.62  % (5283)Termination reason: Refutation
% 1.77/0.62  
% 1.77/0.62  % (5283)Memory used [KB]: 16375
% 1.77/0.62  % (5283)Time elapsed: 0.207 s
% 1.77/0.62  % (5283)------------------------------
% 1.77/0.62  % (5283)------------------------------
% 1.77/0.62  % (5273)Success in time 0.27 s
%------------------------------------------------------------------------------
