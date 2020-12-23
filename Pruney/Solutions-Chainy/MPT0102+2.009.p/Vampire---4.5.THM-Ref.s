%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:57 EST 2020

% Result     : Theorem 8.08s
% Output     : Refutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 607 expanded)
%              Number of leaves         :   14 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :   98 ( 668 expanded)
%              Number of equality atoms :   84 ( 552 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19850,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19848,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f26,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f19848,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f6008,f19666])).

fof(f19666,plain,(
    ! [X57,X58,X56] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X57,X58)),k2_xboole_0(X56,X57)) ),
    inference(superposition,[],[f17149,f8372])).

fof(f8372,plain,(
    ! [X28,X27] : k2_xboole_0(X27,X28) = k2_xboole_0(k4_xboole_0(X27,X28),X28) ),
    inference(forward_demodulation,[],[f8210,f4438])).

fof(f4438,plain,(
    ! [X8,X9] : k4_xboole_0(X8,X9) = k4_xboole_0(k2_xboole_0(X8,X9),X9) ),
    inference(forward_demodulation,[],[f4437,f367])).

fof(f367,plain,(
    ! [X26,X25] : k4_xboole_0(X25,X26) = k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X25,X26))) ),
    inference(forward_demodulation,[],[f330,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f330,plain,(
    ! [X26,X25] : k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(k4_xboole_0(X25,X26),k1_xboole_0) ),
    inference(superposition,[],[f37,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4437,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),X9) ),
    inference(forward_demodulation,[],[f4436,f1660])).

fof(f1660,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X2,k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f1579,f45])).

fof(f1579,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X3),X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X4))) ),
    inference(superposition,[],[f40,f77])).

fof(f77,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f65,f55])).

fof(f55,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f25,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f36,f24])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f65,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f32,f41])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f34,f28])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f4436,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),X9) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k2_xboole_0(X8,X9),X9))) ),
    inference(forward_demodulation,[],[f4365,f24])).

fof(f4365,plain,(
    ! [X8,X9] : k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k2_xboole_0(X8,X9),X9))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X9),k1_xboole_0) ),
    inference(superposition,[],[f37,f3927])).

fof(f3927,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) ),
    inference(resolution,[],[f3904,f30])).

fof(f3904,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X2,X1),X1),X2) ),
    inference(superposition,[],[f3885,f26])).

fof(f3885,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(k2_xboole_0(X24,X25),X24),X25) ),
    inference(forward_demodulation,[],[f3854,f23])).

fof(f3854,plain,(
    ! [X24,X25] : r1_tarski(k4_xboole_0(k2_xboole_0(X24,X25),k2_xboole_0(X24,k1_xboole_0)),X25) ),
    inference(superposition,[],[f415,f41])).

fof(f415,plain,(
    ! [X28,X29,X27] : r1_tarski(k4_xboole_0(X27,k2_xboole_0(X28,k4_xboole_0(X27,k2_xboole_0(X28,X29)))),X29) ),
    inference(forward_demodulation,[],[f398,f32])).

fof(f398,plain,(
    ! [X28,X29,X27] : r1_tarski(k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X27,k2_xboole_0(X28,X29))),X29) ),
    inference(superposition,[],[f344,f32])).

fof(f344,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f25,f37])).

fof(f8210,plain,(
    ! [X28,X27] : k2_xboole_0(X27,X28) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X27,X28),X28),X28) ),
    inference(superposition,[],[f1834,f5074])).

fof(f5074,plain,(
    ! [X10,X11] : k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11 ),
    inference(forward_demodulation,[],[f4987,f1696])).

fof(f1696,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = X5 ),
    inference(forward_demodulation,[],[f1695,f503])).

fof(f503,plain,(
    ! [X37,X38] : k2_xboole_0(X37,k4_xboole_0(X37,X38)) = X37 ),
    inference(forward_demodulation,[],[f502,f24])).

fof(f502,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k1_xboole_0) = k2_xboole_0(X37,k4_xboole_0(X37,X38)) ),
    inference(forward_demodulation,[],[f425,f55])).

fof(f425,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X38))) = k2_xboole_0(X37,k4_xboole_0(X37,X38)) ),
    inference(superposition,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f33,f28])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f1695,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k2_xboole_0(X5,k4_xboole_0(X5,X7)) ),
    inference(forward_demodulation,[],[f1694,f26])).

fof(f1694,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k2_xboole_0(k4_xboole_0(X5,X7),X5) ),
    inference(forward_demodulation,[],[f1598,f24])).

fof(f1598,plain,(
    ! [X6,X7,X5] : k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k2_xboole_0(k4_xboole_0(X5,X7),k4_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f40,f69])).

fof(f69,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f32,f53])).

fof(f4987,plain,(
    ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) ),
    inference(superposition,[],[f37,f4438])).

fof(f1834,plain,(
    ! [X35,X33,X34] : k2_xboole_0(k4_xboole_0(X35,X33),k4_xboole_0(X35,k4_xboole_0(X34,X33))) = X35 ),
    inference(forward_demodulation,[],[f1833,f24])).

fof(f1833,plain,(
    ! [X35,X33,X34] : k2_xboole_0(k4_xboole_0(X35,X33),k4_xboole_0(X35,k4_xboole_0(X34,X33))) = k4_xboole_0(X35,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1802,f41])).

fof(f1802,plain,(
    ! [X35,X33,X34] : k2_xboole_0(k4_xboole_0(X35,X33),k4_xboole_0(X35,k4_xboole_0(X34,X33))) = k4_xboole_0(X35,k4_xboole_0(X33,X33)) ),
    inference(superposition,[],[f39,f1690])).

fof(f1690,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1689,f503])).

fof(f1689,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1688,f26])).

fof(f1688,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1596,f24])).

fof(f1596,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f41])).

fof(f17149,plain,(
    ! [X54,X55,X53] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X55,k4_xboole_0(X53,X54)),k2_xboole_0(X55,X53)) ),
    inference(superposition,[],[f16792,f527])).

fof(f527,plain,(
    ! [X37,X38] : k2_xboole_0(k4_xboole_0(X37,X38),X37) = X37 ),
    inference(forward_demodulation,[],[f526,f24])).

fof(f526,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X37,X38),X37) ),
    inference(forward_demodulation,[],[f525,f41])).

fof(f525,plain,(
    ! [X37,X38] : k2_xboole_0(k4_xboole_0(X37,X38),X37) = k4_xboole_0(X37,k4_xboole_0(X38,X38)) ),
    inference(forward_demodulation,[],[f441,f24])).

fof(f441,plain,(
    ! [X37,X38] : k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X38,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X37,X38),X37) ),
    inference(superposition,[],[f39,f24])).

fof(f16792,plain,(
    ! [X19,X17,X18] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,k2_xboole_0(X18,X19))) ),
    inference(superposition,[],[f81,f77])).

fof(f81,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) = k4_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X11,X12))) ),
    inference(forward_demodulation,[],[f80,f32])).

fof(f80,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) ),
    inference(forward_demodulation,[],[f68,f32])).

fof(f68,plain,(
    ! [X12,X10,X11,X9] : k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X12) ),
    inference(superposition,[],[f32,f32])).

fof(f6008,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f6006,f37])).

fof(f6006,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f35,f5912])).

fof(f5912,plain,(
    ! [X14,X15,X13] : k4_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(k4_xboole_0(X13,X14),X15)) ),
    inference(superposition,[],[f32,f5074])).

fof(f35,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f21,f28,f29,f29])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f21,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (14434)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (14426)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (14429)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (14425)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (14436)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (14432)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (14424)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (14422)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (14423)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (14438)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.49  % (14439)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (14428)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (14437)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (14430)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (14435)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (14431)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.51  % (14427)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.52  % (14433)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.53  % (14433)Refutation not found, incomplete strategy% (14433)------------------------------
% 0.20/0.53  % (14433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (14433)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (14433)Memory used [KB]: 10490
% 0.20/0.53  % (14433)Time elapsed: 0.116 s
% 0.20/0.53  % (14433)------------------------------
% 0.20/0.53  % (14433)------------------------------
% 4.94/1.03  % (14426)Time limit reached!
% 4.94/1.03  % (14426)------------------------------
% 4.94/1.03  % (14426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/1.03  % (14426)Termination reason: Time limit
% 4.94/1.03  
% 4.94/1.03  % (14426)Memory used [KB]: 17014
% 4.94/1.03  % (14426)Time elapsed: 0.613 s
% 4.94/1.03  % (14426)------------------------------
% 4.94/1.03  % (14426)------------------------------
% 8.08/1.40  % (14431)Refutation found. Thanks to Tanya!
% 8.08/1.40  % SZS status Theorem for theBenchmark
% 8.08/1.40  % SZS output start Proof for theBenchmark
% 8.08/1.40  fof(f19850,plain,(
% 8.08/1.40    $false),
% 8.08/1.40    inference(subsumption_resolution,[],[f19848,f45])).
% 8.08/1.40  fof(f45,plain,(
% 8.08/1.40    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 8.08/1.40    inference(superposition,[],[f26,f23])).
% 8.08/1.40  fof(f23,plain,(
% 8.08/1.40    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.08/1.40    inference(cnf_transformation,[],[f6])).
% 8.08/1.40  fof(f6,axiom,(
% 8.08/1.40    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 8.08/1.40  fof(f26,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.08/1.40    inference(cnf_transformation,[],[f1])).
% 8.08/1.40  fof(f1,axiom,(
% 8.08/1.40    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 8.08/1.40  fof(f19848,plain,(
% 8.08/1.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 8.08/1.40    inference(backward_demodulation,[],[f6008,f19666])).
% 8.08/1.40  fof(f19666,plain,(
% 8.08/1.40    ( ! [X57,X58,X56] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X56,X57),k4_xboole_0(X57,X58)),k2_xboole_0(X56,X57))) )),
% 8.08/1.40    inference(superposition,[],[f17149,f8372])).
% 8.08/1.40  fof(f8372,plain,(
% 8.08/1.40    ( ! [X28,X27] : (k2_xboole_0(X27,X28) = k2_xboole_0(k4_xboole_0(X27,X28),X28)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f8210,f4438])).
% 8.08/1.40  fof(f4438,plain,(
% 8.08/1.40    ( ! [X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(k2_xboole_0(X8,X9),X9)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f4437,f367])).
% 8.08/1.40  fof(f367,plain,(
% 8.08/1.40    ( ! [X26,X25] : (k4_xboole_0(X25,X26) = k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X25,X26)))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f330,f24])).
% 8.08/1.40  fof(f24,plain,(
% 8.08/1.40    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.08/1.40    inference(cnf_transformation,[],[f9])).
% 8.08/1.40  fof(f9,axiom,(
% 8.08/1.40    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 8.08/1.40  fof(f330,plain,(
% 8.08/1.40    ( ! [X26,X25] : (k4_xboole_0(X25,k4_xboole_0(X25,k4_xboole_0(X25,X26))) = k4_xboole_0(k4_xboole_0(X25,X26),k1_xboole_0)) )),
% 8.08/1.40    inference(superposition,[],[f37,f53])).
% 8.08/1.40  fof(f53,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 8.08/1.40    inference(resolution,[],[f30,f25])).
% 8.08/1.40  fof(f25,plain,(
% 8.08/1.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 8.08/1.40    inference(cnf_transformation,[],[f8])).
% 8.08/1.40  fof(f8,axiom,(
% 8.08/1.40    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 8.08/1.40  fof(f30,plain,(
% 8.08/1.40    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 8.08/1.40    inference(cnf_transformation,[],[f18])).
% 8.08/1.40  fof(f18,plain,(
% 8.08/1.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 8.08/1.40    inference(ennf_transformation,[],[f16])).
% 8.08/1.40  fof(f16,plain,(
% 8.08/1.40    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 8.08/1.40    inference(unused_predicate_definition_removal,[],[f4])).
% 8.08/1.40  fof(f4,axiom,(
% 8.08/1.40    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 8.08/1.40  fof(f37,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.08/1.40    inference(definition_unfolding,[],[f27,f28,f28])).
% 8.08/1.40  fof(f28,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.08/1.40    inference(cnf_transformation,[],[f11])).
% 8.08/1.40  fof(f11,axiom,(
% 8.08/1.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 8.08/1.40  fof(f27,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.08/1.40    inference(cnf_transformation,[],[f2])).
% 8.08/1.40  fof(f2,axiom,(
% 8.08/1.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.08/1.40  fof(f4437,plain,(
% 8.08/1.40    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))) = k4_xboole_0(k2_xboole_0(X8,X9),X9)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f4436,f1660])).
% 8.08/1.40  fof(f1660,plain,(
% 8.08/1.40    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X3),X4)) = k4_xboole_0(X2,k4_xboole_0(X2,X4))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1579,f45])).
% 8.08/1.40  fof(f1579,plain,(
% 8.08/1.40    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(k2_xboole_0(X2,X3),X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k4_xboole_0(X2,X4)))) )),
% 8.08/1.40    inference(superposition,[],[f40,f77])).
% 8.08/1.40  fof(f77,plain,(
% 8.08/1.40    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f65,f55])).
% 8.08/1.40  fof(f55,plain,(
% 8.08/1.40    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 8.08/1.40    inference(resolution,[],[f30,f44])).
% 8.08/1.40  fof(f44,plain,(
% 8.08/1.40    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 8.08/1.40    inference(superposition,[],[f25,f41])).
% 8.08/1.40  fof(f41,plain,(
% 8.08/1.40    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 8.08/1.40    inference(backward_demodulation,[],[f36,f24])).
% 8.08/1.40  fof(f36,plain,(
% 8.08/1.40    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 8.08/1.40    inference(definition_unfolding,[],[f22,f28])).
% 8.08/1.40  fof(f22,plain,(
% 8.08/1.40    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 8.08/1.40    inference(cnf_transformation,[],[f7])).
% 8.08/1.40  fof(f7,axiom,(
% 8.08/1.40    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 8.08/1.40  fof(f65,plain,(
% 8.08/1.40    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 8.08/1.40    inference(superposition,[],[f32,f41])).
% 8.08/1.40  fof(f32,plain,(
% 8.08/1.40    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 8.08/1.40    inference(cnf_transformation,[],[f10])).
% 8.08/1.40  fof(f10,axiom,(
% 8.08/1.40    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 8.08/1.40  fof(f40,plain,(
% 8.08/1.40    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 8.08/1.40    inference(definition_unfolding,[],[f34,f28])).
% 8.08/1.40  fof(f34,plain,(
% 8.08/1.40    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 8.08/1.40    inference(cnf_transformation,[],[f13])).
% 8.08/1.40  fof(f13,axiom,(
% 8.08/1.40    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 8.08/1.40  fof(f4436,plain,(
% 8.08/1.40    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),X9) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k2_xboole_0(X8,X9),X9)))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f4365,f24])).
% 8.08/1.40  fof(f4365,plain,(
% 8.08/1.40    ( ! [X8,X9] : (k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k2_xboole_0(X8,X9),X9))) = k4_xboole_0(k4_xboole_0(k2_xboole_0(X8,X9),X9),k1_xboole_0)) )),
% 8.08/1.40    inference(superposition,[],[f37,f3927])).
% 8.08/1.40  fof(f3927,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0)) )),
% 8.08/1.40    inference(resolution,[],[f3904,f30])).
% 8.08/1.40  fof(f3904,plain,(
% 8.08/1.40    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X2,X1),X1),X2)) )),
% 8.08/1.40    inference(superposition,[],[f3885,f26])).
% 8.08/1.40  fof(f3885,plain,(
% 8.08/1.40    ( ! [X24,X25] : (r1_tarski(k4_xboole_0(k2_xboole_0(X24,X25),X24),X25)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f3854,f23])).
% 8.08/1.40  fof(f3854,plain,(
% 8.08/1.40    ( ! [X24,X25] : (r1_tarski(k4_xboole_0(k2_xboole_0(X24,X25),k2_xboole_0(X24,k1_xboole_0)),X25)) )),
% 8.08/1.40    inference(superposition,[],[f415,f41])).
% 8.08/1.40  fof(f415,plain,(
% 8.08/1.40    ( ! [X28,X29,X27] : (r1_tarski(k4_xboole_0(X27,k2_xboole_0(X28,k4_xboole_0(X27,k2_xboole_0(X28,X29)))),X29)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f398,f32])).
% 8.08/1.40  fof(f398,plain,(
% 8.08/1.40    ( ! [X28,X29,X27] : (r1_tarski(k4_xboole_0(k4_xboole_0(X27,X28),k4_xboole_0(X27,k2_xboole_0(X28,X29))),X29)) )),
% 8.08/1.40    inference(superposition,[],[f344,f32])).
% 8.08/1.40  fof(f344,plain,(
% 8.08/1.40    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 8.08/1.40    inference(superposition,[],[f25,f37])).
% 8.08/1.40  fof(f8210,plain,(
% 8.08/1.40    ( ! [X28,X27] : (k2_xboole_0(X27,X28) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X27,X28),X28),X28)) )),
% 8.08/1.40    inference(superposition,[],[f1834,f5074])).
% 8.08/1.40  fof(f5074,plain,(
% 8.08/1.40    ( ! [X10,X11] : (k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11)) = X11) )),
% 8.08/1.40    inference(forward_demodulation,[],[f4987,f1696])).
% 8.08/1.40  fof(f1696,plain,(
% 8.08/1.40    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = X5) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1695,f503])).
% 8.08/1.40  fof(f503,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k2_xboole_0(X37,k4_xboole_0(X37,X38)) = X37) )),
% 8.08/1.40    inference(forward_demodulation,[],[f502,f24])).
% 8.08/1.40  fof(f502,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k4_xboole_0(X37,k1_xboole_0) = k2_xboole_0(X37,k4_xboole_0(X37,X38))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f425,f55])).
% 8.08/1.40  fof(f425,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k4_xboole_0(X37,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X38))) = k2_xboole_0(X37,k4_xboole_0(X37,X38))) )),
% 8.08/1.40    inference(superposition,[],[f39,f24])).
% 8.08/1.40  fof(f39,plain,(
% 8.08/1.40    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 8.08/1.40    inference(definition_unfolding,[],[f33,f28])).
% 8.08/1.40  fof(f33,plain,(
% 8.08/1.40    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 8.08/1.40    inference(cnf_transformation,[],[f5])).
% 8.08/1.40  fof(f5,axiom,(
% 8.08/1.40    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 8.08/1.40  fof(f1695,plain,(
% 8.08/1.40    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k2_xboole_0(X5,k4_xboole_0(X5,X7))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1694,f26])).
% 8.08/1.40  fof(f1694,plain,(
% 8.08/1.40    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k2_xboole_0(k4_xboole_0(X5,X7),X5)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1598,f24])).
% 8.08/1.40  fof(f1598,plain,(
% 8.08/1.40    ( ! [X6,X7,X5] : (k4_xboole_0(X5,k4_xboole_0(X7,k2_xboole_0(X6,X5))) = k2_xboole_0(k4_xboole_0(X5,X7),k4_xboole_0(X5,k1_xboole_0))) )),
% 8.08/1.40    inference(superposition,[],[f40,f69])).
% 8.08/1.40  fof(f69,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 8.08/1.40    inference(superposition,[],[f32,f53])).
% 8.08/1.40  fof(f4987,plain,(
% 8.08/1.40    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k2_xboole_0(X10,X11))) = k4_xboole_0(k2_xboole_0(X10,X11),k4_xboole_0(X10,X11))) )),
% 8.08/1.40    inference(superposition,[],[f37,f4438])).
% 8.08/1.40  fof(f1834,plain,(
% 8.08/1.40    ( ! [X35,X33,X34] : (k2_xboole_0(k4_xboole_0(X35,X33),k4_xboole_0(X35,k4_xboole_0(X34,X33))) = X35) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1833,f24])).
% 8.08/1.40  fof(f1833,plain,(
% 8.08/1.40    ( ! [X35,X33,X34] : (k2_xboole_0(k4_xboole_0(X35,X33),k4_xboole_0(X35,k4_xboole_0(X34,X33))) = k4_xboole_0(X35,k1_xboole_0)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1802,f41])).
% 8.08/1.40  fof(f1802,plain,(
% 8.08/1.40    ( ! [X35,X33,X34] : (k2_xboole_0(k4_xboole_0(X35,X33),k4_xboole_0(X35,k4_xboole_0(X34,X33))) = k4_xboole_0(X35,k4_xboole_0(X33,X33))) )),
% 8.08/1.40    inference(superposition,[],[f39,f1690])).
% 8.08/1.40  fof(f1690,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1689,f503])).
% 8.08/1.40  fof(f1689,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1688,f26])).
% 8.08/1.40  fof(f1688,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f1596,f24])).
% 8.08/1.40  fof(f1596,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 8.08/1.40    inference(superposition,[],[f40,f41])).
% 8.08/1.40  fof(f17149,plain,(
% 8.08/1.40    ( ! [X54,X55,X53] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X55,k4_xboole_0(X53,X54)),k2_xboole_0(X55,X53))) )),
% 8.08/1.40    inference(superposition,[],[f16792,f527])).
% 8.08/1.40  fof(f527,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k2_xboole_0(k4_xboole_0(X37,X38),X37) = X37) )),
% 8.08/1.40    inference(forward_demodulation,[],[f526,f24])).
% 8.08/1.40  fof(f526,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k4_xboole_0(X37,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X37,X38),X37)) )),
% 8.08/1.40    inference(forward_demodulation,[],[f525,f41])).
% 8.08/1.40  fof(f525,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k2_xboole_0(k4_xboole_0(X37,X38),X37) = k4_xboole_0(X37,k4_xboole_0(X38,X38))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f441,f24])).
% 8.08/1.40  fof(f441,plain,(
% 8.08/1.40    ( ! [X37,X38] : (k4_xboole_0(X37,k4_xboole_0(X38,k4_xboole_0(X38,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X37,X38),X37)) )),
% 8.08/1.40    inference(superposition,[],[f39,f24])).
% 8.08/1.40  fof(f16792,plain,(
% 8.08/1.40    ( ! [X19,X17,X18] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X17,X18),k2_xboole_0(X17,k2_xboole_0(X18,X19)))) )),
% 8.08/1.40    inference(superposition,[],[f81,f77])).
% 8.08/1.40  fof(f81,plain,(
% 8.08/1.40    ( ! [X12,X10,X11,X9] : (k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12)) = k4_xboole_0(X9,k2_xboole_0(X10,k2_xboole_0(X11,X12)))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f80,f32])).
% 8.08/1.40  fof(f80,plain,(
% 8.08/1.40    ( ! [X12,X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(X9,k2_xboole_0(k2_xboole_0(X10,X11),X12))) )),
% 8.08/1.40    inference(forward_demodulation,[],[f68,f32])).
% 8.08/1.40  fof(f68,plain,(
% 8.08/1.40    ( ! [X12,X10,X11,X9] : (k4_xboole_0(k4_xboole_0(X9,X10),k2_xboole_0(X11,X12)) = k4_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X12)) )),
% 8.08/1.40    inference(superposition,[],[f32,f32])).
% 8.08/1.40  fof(f6008,plain,(
% 8.08/1.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 8.08/1.40    inference(forward_demodulation,[],[f6006,f37])).
% 8.08/1.40  fof(f6006,plain,(
% 8.08/1.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))),
% 8.08/1.40    inference(backward_demodulation,[],[f35,f5912])).
% 8.08/1.40  fof(f5912,plain,(
% 8.08/1.40    ( ! [X14,X15,X13] : (k4_xboole_0(X14,X15) = k4_xboole_0(k2_xboole_0(X13,X14),k2_xboole_0(k4_xboole_0(X13,X14),X15))) )),
% 8.08/1.40    inference(superposition,[],[f32,f5074])).
% 8.08/1.40  fof(f35,plain,(
% 8.08/1.40    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 8.08/1.40    inference(definition_unfolding,[],[f21,f28,f29,f29])).
% 8.08/1.40  fof(f29,plain,(
% 8.08/1.40    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 8.08/1.40    inference(cnf_transformation,[],[f3])).
% 8.08/1.40  fof(f3,axiom,(
% 8.08/1.40    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 8.08/1.40  fof(f21,plain,(
% 8.08/1.40    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.08/1.40    inference(cnf_transformation,[],[f20])).
% 8.08/1.40  fof(f20,plain,(
% 8.08/1.40    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.08/1.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19])).
% 8.08/1.40  fof(f19,plain,(
% 8.08/1.40    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.08/1.40    introduced(choice_axiom,[])).
% 8.08/1.40  fof(f17,plain,(
% 8.08/1.40    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.08/1.40    inference(ennf_transformation,[],[f15])).
% 8.08/1.40  fof(f15,negated_conjecture,(
% 8.08/1.40    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.08/1.40    inference(negated_conjecture,[],[f14])).
% 8.08/1.40  fof(f14,conjecture,(
% 8.08/1.40    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.08/1.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 8.08/1.40  % SZS output end Proof for theBenchmark
% 8.08/1.40  % (14431)------------------------------
% 8.08/1.40  % (14431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.08/1.40  % (14431)Termination reason: Refutation
% 8.08/1.40  
% 8.08/1.40  % (14431)Memory used [KB]: 25074
% 8.08/1.40  % (14431)Time elapsed: 0.998 s
% 8.08/1.40  % (14431)------------------------------
% 8.08/1.40  % (14431)------------------------------
% 8.57/1.43  % (14421)Success in time 1.074 s
%------------------------------------------------------------------------------
