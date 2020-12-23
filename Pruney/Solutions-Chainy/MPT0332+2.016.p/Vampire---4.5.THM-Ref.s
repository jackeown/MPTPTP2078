%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:10 EST 2020

% Result     : Theorem 2.11s
% Output     : Refutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :  148 (19352 expanded)
%              Number of leaves         :   21 (6001 expanded)
%              Depth                    :   36
%              Number of atoms          :  206 (25109 expanded)
%              Number of equality atoms :  117 (15512 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5541,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f5540])).

fof(f5540,plain,(
    sK2 != sK2 ),
    inference(superposition,[],[f5058,f998])).

fof(f998,plain,(
    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(resolution,[],[f592,f34])).

fof(f34,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f592,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | sK2 = k4_xboole_0(sK2,k2_enumset1(X1,X1,X1,sK1)) ) ),
    inference(resolution,[],[f71,f35])).

fof(f35,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f58,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f5058,plain,(
    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f5008,f3297])).

fof(f3297,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X1,X0),X0) ),
    inference(forward_demodulation,[],[f3296,f894])).

fof(f894,plain,(
    ! [X10] : k5_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(forward_demodulation,[],[f876,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f876,plain,(
    ! [X10] : k5_xboole_0(X10,k4_xboole_0(k1_xboole_0,X10)) = X10 ),
    inference(superposition,[],[f803,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f803,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X0)) = X0 ),
    inference(forward_demodulation,[],[f802,f61])).

fof(f61,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f802,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X0)) ),
    inference(forward_demodulation,[],[f780,f202])).

fof(f202,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k3_xboole_0(X7,X8),X7) ),
    inference(superposition,[],[f46,f89])).

fof(f89,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f61,f60])).

fof(f60,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f780,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f72,f89])).

fof(f72,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f47,f43,f43])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f3296,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3288,f74])).

fof(f3288,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f2037,f3282])).

fof(f3282,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(backward_demodulation,[],[f1966,f3222])).

fof(f3222,plain,(
    ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10) ),
    inference(superposition,[],[f1984,f38])).

fof(f1984,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k3_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(forward_demodulation,[],[f1979,f61])).

fof(f1979,plain,(
    ! [X0,X1] : k3_xboole_0(k4_xboole_0(X0,X0),X1) = k3_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X0,X0)))) ),
    inference(resolution,[],[f1664,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f50,f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f1664,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(superposition,[],[f282,f1339])).

fof(f1339,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k3_xboole_0(k4_xboole_0(X1,X0),X1) ),
    inference(backward_demodulation,[],[f927,f1325])).

fof(f1325,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f1209,f1232])).

fof(f1232,plain,(
    ! [X14] : k5_xboole_0(k1_xboole_0,X14) = X14 ),
    inference(backward_demodulation,[],[f941,f1209])).

fof(f941,plain,(
    ! [X14] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X14) ),
    inference(backward_demodulation,[],[f656,f894])).

fof(f656,plain,(
    ! [X14] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X14),k1_xboole_0) ),
    inference(forward_demodulation,[],[f643,f74])).

fof(f643,plain,(
    ! [X14] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X14))) ),
    inference(superposition,[],[f62,f498])).

fof(f498,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f267,f61])).

fof(f267,plain,(
    ! [X47,X48] : k3_xboole_0(k1_xboole_0,X47) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X48,k4_xboole_0(X47,X48))) ),
    inference(resolution,[],[f66,f84])).

fof(f84,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f43,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f1209,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f809,f89])).

fof(f809,plain,(
    ! [X17,X16] : k3_xboole_0(X16,X17) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X16,X17),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f808,f617])).

fof(f617,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(resolution,[],[f599,f66])).

fof(f599,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f576,f139])).

fof(f139,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f138,f41])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X0),X0)
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f68,f60])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f54,f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f576,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | r1_xboole_0(X4,k1_xboole_0) ) ),
    inference(resolution,[],[f531,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f43])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f531,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X5,k5_xboole_0(k1_xboole_0,X4))
      | r1_xboole_0(X5,k1_xboole_0) ) ),
    inference(superposition,[],[f56,f498])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f808,plain,(
    ! [X17,X16] : k3_xboole_0(X16,k5_xboole_0(k1_xboole_0,k4_xboole_0(X17,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X16,X17),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f786,f199])).

fof(f199,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f46,f38])).

fof(f786,plain,(
    ! [X17,X16] : k3_xboole_0(X16,k5_xboole_0(k1_xboole_0,k4_xboole_0(X17,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X16,k4_xboole_0(X17,k1_xboole_0))) ),
    inference(superposition,[],[f72,f38])).

fof(f927,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k3_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f404,f894])).

fof(f404,plain,(
    ! [X0,X1] : k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f64,f74])).

fof(f64,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f48,f43])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f282,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X1)) ),
    inference(superposition,[],[f215,f89])).

fof(f215,plain,(
    ! [X47,X48,X49] : r1_xboole_0(k3_xboole_0(X47,k4_xboole_0(X48,X49)),k3_xboole_0(X47,X49)) ),
    inference(superposition,[],[f147,f46])).

fof(f147,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f139,f53])).

fof(f1966,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f1960,f1693])).

fof(f1693,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(backward_demodulation,[],[f64,f1692])).

fof(f1692,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X5,X6),X7) ),
    inference(forward_demodulation,[],[f1667,f1434])).

fof(f1434,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k4_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(backward_demodulation,[],[f198,f1433])).

fof(f1433,plain,(
    ! [X6,X7] : k4_xboole_0(X6,X7) = k3_xboole_0(X6,k4_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f1432,f1325])).

fof(f1432,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X6,k4_xboole_0(X7,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1384,f1232])).

fof(f1384,plain,(
    ! [X6,X7] : k3_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X6,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0))) ),
    inference(superposition,[],[f64,f1325])).

fof(f198,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k4_xboole_0(X7,X8)) = k4_xboole_0(X7,k3_xboole_0(X7,X8)) ),
    inference(superposition,[],[f46,f89])).

fof(f1667,plain,(
    ! [X6,X7,X5] : k3_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k4_xboole_0(X5,X6),X7)) ),
    inference(superposition,[],[f46,f1339])).

fof(f1960,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(backward_demodulation,[],[f1351,f1903])).

fof(f1903,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f1693,f60])).

fof(f1351,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X6))) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(backward_demodulation,[],[f402,f1339])).

fof(f402,plain,(
    ! [X6,X5] : k4_xboole_0(k3_xboole_0(k4_xboole_0(X5,X6),X5),k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X6))) ),
    inference(superposition,[],[f64,f202])).

fof(f2037,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X1)) ),
    inference(backward_demodulation,[],[f1755,f2035])).

fof(f2035,plain,(
    ! [X103,X101,X102] : k4_xboole_0(k4_xboole_0(X103,X102),k4_xboole_0(X101,X102)) = k4_xboole_0(k4_xboole_0(X103,X102),X101) ),
    inference(forward_demodulation,[],[f2031,f1693])).

fof(f2031,plain,(
    ! [X103,X101,X102] : k4_xboole_0(k4_xboole_0(X103,X102),k4_xboole_0(X101,X102)) = k4_xboole_0(X103,k5_xboole_0(X102,k4_xboole_0(X101,X102))) ),
    inference(superposition,[],[f1693,f1903])).

fof(f1755,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f848,f1693])).

fof(f848,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f65,f60])).

fof(f65,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))))) ),
    inference(definition_unfolding,[],[f49,f43,f43,f43])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f5008,plain,(
    sK2 != k4_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f59,f4911])).

fof(f4911,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(superposition,[],[f4559,f998])).

fof(f4559,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1 ),
    inference(forward_demodulation,[],[f4531,f1325])).

fof(f4531,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(backward_demodulation,[],[f2042,f4438])).

fof(f4438,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f3827,f1903])).

fof(f3827,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),X0) ),
    inference(forward_demodulation,[],[f3768,f3222])).

fof(f3768,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),X0) ),
    inference(superposition,[],[f3299,f803])).

fof(f3299,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f3291,f1232])).

fof(f3291,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f2140,f3282])).

fof(f2140,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X1,X0)) ),
    inference(backward_demodulation,[],[f2036,f2133])).

fof(f2133,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X19,X17) = k4_xboole_0(k4_xboole_0(X19,X17),k4_xboole_0(X17,X18)) ),
    inference(superposition,[],[f1693,f1446])).

fof(f1446,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X5)) = X5 ),
    inference(backward_demodulation,[],[f873,f1434])).

fof(f873,plain,(
    ! [X6,X5] : k5_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,k3_xboole_0(X5,X6)),X5)) = X5 ),
    inference(superposition,[],[f803,f198])).

fof(f2036,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ),
    inference(backward_demodulation,[],[f1756,f2035])).

fof(f1756,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,X1),X0))) ),
    inference(backward_demodulation,[],[f838,f1693])).

fof(f838,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) ),
    inference(superposition,[],[f65,f60])).

fof(f2042,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X1)) ),
    inference(superposition,[],[f1434,f202])).

fof(f59,plain,(
    sK2 != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f36,f43,f44,f44])).

fof(f36,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:24:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10775)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (10774)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (10776)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (10786)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (10782)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (10772)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (10787)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (10778)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (10773)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (10779)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (10783)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (10784)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (10785)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (10781)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10788)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (10780)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (10777)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.52  % (10789)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.11/0.67  % (10773)Refutation found. Thanks to Tanya!
% 2.11/0.67  % SZS status Theorem for theBenchmark
% 2.11/0.67  % SZS output start Proof for theBenchmark
% 2.11/0.67  fof(f5541,plain,(
% 2.11/0.67    $false),
% 2.11/0.67    inference(trivial_inequality_removal,[],[f5540])).
% 2.11/0.67  fof(f5540,plain,(
% 2.11/0.67    sK2 != sK2),
% 2.11/0.67    inference(superposition,[],[f5058,f998])).
% 2.11/0.67  fof(f998,plain,(
% 2.11/0.67    sK2 = k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.11/0.67    inference(resolution,[],[f592,f34])).
% 2.11/0.67  fof(f34,plain,(
% 2.11/0.67    ~r2_hidden(sK0,sK2)),
% 2.11/0.67    inference(cnf_transformation,[],[f31])).
% 2.11/0.67  fof(f31,plain,(
% 2.11/0.67    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.11/0.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f30])).
% 2.11/0.67  fof(f30,plain,(
% 2.11/0.67    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.11/0.67    introduced(choice_axiom,[])).
% 2.11/0.67  fof(f23,plain,(
% 2.11/0.67    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.67    inference(ennf_transformation,[],[f21])).
% 2.11/0.67  fof(f21,negated_conjecture,(
% 2.11/0.67    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.67    inference(negated_conjecture,[],[f20])).
% 2.11/0.67  fof(f20,conjecture,(
% 2.11/0.67    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 2.11/0.67  fof(f592,plain,(
% 2.11/0.67    ( ! [X1] : (r2_hidden(X1,sK2) | sK2 = k4_xboole_0(sK2,k2_enumset1(X1,X1,X1,sK1))) )),
% 2.11/0.67    inference(resolution,[],[f71,f35])).
% 2.11/0.67  fof(f35,plain,(
% 2.11/0.67    ~r2_hidden(sK1,sK2)),
% 2.11/0.67    inference(cnf_transformation,[],[f31])).
% 2.11/0.67  fof(f71,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_xboole_0(X2,k2_enumset1(X0,X0,X0,X1)) = X2) )),
% 2.11/0.67    inference(definition_unfolding,[],[f58,f44])).
% 2.11/0.67  fof(f44,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f18])).
% 2.11/0.67  fof(f18,axiom,(
% 2.11/0.67    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 2.11/0.67  fof(f58,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f29])).
% 2.11/0.67  fof(f29,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 2.11/0.67    inference(ennf_transformation,[],[f19])).
% 2.11/0.67  fof(f19,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 2.11/0.67  fof(f5058,plain,(
% 2.11/0.67    sK2 != k4_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.11/0.67    inference(superposition,[],[f5008,f3297])).
% 2.11/0.67  fof(f3297,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X1,X0),X0)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f3296,f894])).
% 2.11/0.67  fof(f894,plain,(
% 2.11/0.67    ( ! [X10] : (k5_xboole_0(X10,k1_xboole_0) = X10) )),
% 2.11/0.67    inference(forward_demodulation,[],[f876,f74])).
% 2.11/0.67  fof(f74,plain,(
% 2.11/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.11/0.67    inference(resolution,[],[f39,f41])).
% 2.11/0.67  fof(f41,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f9])).
% 2.11/0.67  fof(f9,axiom,(
% 2.11/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.11/0.67  fof(f39,plain,(
% 2.11/0.67    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.11/0.67    inference(cnf_transformation,[],[f24])).
% 2.11/0.67  fof(f24,plain,(
% 2.11/0.67    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.11/0.67    inference(ennf_transformation,[],[f10])).
% 2.11/0.67  fof(f10,axiom,(
% 2.11/0.67    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.11/0.67  fof(f876,plain,(
% 2.11/0.67    ( ! [X10] : (k5_xboole_0(X10,k4_xboole_0(k1_xboole_0,X10)) = X10) )),
% 2.11/0.67    inference(superposition,[],[f803,f38])).
% 2.11/0.67  fof(f38,plain,(
% 2.11/0.67    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f7])).
% 2.11/0.67  fof(f7,axiom,(
% 2.11/0.67    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.11/0.67  fof(f803,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X0)) = X0) )),
% 2.11/0.67    inference(forward_demodulation,[],[f802,f61])).
% 2.11/0.67  fof(f61,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = X0) )),
% 2.11/0.67    inference(definition_unfolding,[],[f42,f43])).
% 2.11/0.67  fof(f43,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f16])).
% 2.11/0.67  fof(f16,axiom,(
% 2.11/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.11/0.67  fof(f42,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.11/0.67    inference(cnf_transformation,[],[f5])).
% 2.11/0.67  fof(f5,axiom,(
% 2.11/0.67    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 2.11/0.67  fof(f802,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k3_xboole_0(X0,X1),X0))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f780,f202])).
% 2.11/0.67  fof(f202,plain,(
% 2.11/0.67    ( ! [X8,X7] : (k3_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k3_xboole_0(X7,X8),X7)) )),
% 2.11/0.67    inference(superposition,[],[f46,f89])).
% 2.11/0.67  fof(f89,plain,(
% 2.11/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.11/0.67    inference(superposition,[],[f61,f60])).
% 2.11/0.67  fof(f60,plain,(
% 2.11/0.67    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.11/0.67    inference(definition_unfolding,[],[f40,f43])).
% 2.11/0.67  fof(f40,plain,(
% 2.11/0.67    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.11/0.67    inference(cnf_transformation,[],[f22])).
% 2.11/0.67  fof(f22,plain,(
% 2.11/0.67    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.11/0.67    inference(rectify,[],[f1])).
% 2.11/0.67  fof(f1,axiom,(
% 2.11/0.67    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.11/0.67  fof(f46,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f12])).
% 2.11/0.67  fof(f12,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 2.11/0.67  fof(f780,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k3_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.11/0.67    inference(superposition,[],[f72,f89])).
% 2.11/0.67  fof(f72,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X2,X1)))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f63,f46])).
% 2.11/0.67  fof(f63,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k5_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(k3_xboole_0(X0,X2),k3_xboole_0(X0,X1)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f47,f43,f43])).
% 2.11/0.67  fof(f47,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f6])).
% 2.11/0.67  fof(f6,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 2.11/0.67  fof(f3296,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f3288,f74])).
% 2.11/0.67  fof(f3288,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k1_xboole_0,X1))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f2037,f3282])).
% 2.11/0.67  fof(f3282,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.11/0.67    inference(backward_demodulation,[],[f1966,f3222])).
% 2.11/0.67  fof(f3222,plain,(
% 2.11/0.67    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,X10)) )),
% 2.11/0.67    inference(superposition,[],[f1984,f38])).
% 2.11/0.67  fof(f1984,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k3_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f1979,f61])).
% 2.11/0.67  fof(f1979,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X0),X1) = k3_xboole_0(k4_xboole_0(X0,X0),k5_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k4_xboole_0(X0,X0))))) )),
% 2.11/0.67    inference(resolution,[],[f1664,f66])).
% 2.11/0.67  fof(f66,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X2) = k3_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f50,f43])).
% 2.11/0.67  fof(f50,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f25])).
% 2.11/0.67  fof(f25,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 2.11/0.67    inference(ennf_transformation,[],[f14])).
% 2.11/0.67  fof(f14,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).
% 2.11/0.67  fof(f1664,plain,(
% 2.11/0.67    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 2.11/0.67    inference(superposition,[],[f282,f1339])).
% 2.11/0.67  fof(f1339,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k3_xboole_0(k4_xboole_0(X1,X0),X1)) )),
% 2.11/0.67    inference(backward_demodulation,[],[f927,f1325])).
% 2.11/0.67  fof(f1325,plain,(
% 2.11/0.67    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.11/0.67    inference(superposition,[],[f1209,f1232])).
% 2.11/0.67  fof(f1232,plain,(
% 2.11/0.67    ( ! [X14] : (k5_xboole_0(k1_xboole_0,X14) = X14) )),
% 2.11/0.67    inference(backward_demodulation,[],[f941,f1209])).
% 2.11/0.67  fof(f941,plain,(
% 2.11/0.67    ( ! [X14] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) = k5_xboole_0(k1_xboole_0,X14)) )),
% 2.11/0.67    inference(backward_demodulation,[],[f656,f894])).
% 2.11/0.67  fof(f656,plain,(
% 2.11/0.67    ( ! [X14] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X14),k1_xboole_0)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f643,f74])).
% 2.11/0.67  fof(f643,plain,(
% 2.11/0.67    ( ! [X14] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X14),k4_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X14)))) )),
% 2.11/0.67    inference(superposition,[],[f62,f498])).
% 2.11/0.67  fof(f498,plain,(
% 2.11/0.67    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 2.11/0.67    inference(superposition,[],[f267,f61])).
% 2.11/0.67  fof(f267,plain,(
% 2.11/0.67    ( ! [X47,X48] : (k3_xboole_0(k1_xboole_0,X47) = k3_xboole_0(k1_xboole_0,k5_xboole_0(X48,k4_xboole_0(X47,X48)))) )),
% 2.11/0.67    inference(resolution,[],[f66,f84])).
% 2.11/0.67  fof(f84,plain,(
% 2.11/0.67    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.11/0.67    inference(resolution,[],[f53,f37])).
% 2.11/0.67  fof(f37,plain,(
% 2.11/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f8])).
% 2.11/0.67  fof(f8,axiom,(
% 2.11/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.11/0.67  fof(f53,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f27])).
% 2.11/0.67  fof(f27,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.11/0.67    inference(ennf_transformation,[],[f2])).
% 2.11/0.67  fof(f2,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.11/0.67  fof(f62,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f45,f43,f43])).
% 2.11/0.67  fof(f45,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f15])).
% 2.11/0.67  fof(f15,axiom,(
% 2.11/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.11/0.67  fof(f1209,plain,(
% 2.11/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.11/0.67    inference(superposition,[],[f809,f89])).
% 2.11/0.67  fof(f809,plain,(
% 2.11/0.67    ( ! [X17,X16] : (k3_xboole_0(X16,X17) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X16,X17),k1_xboole_0))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f808,f617])).
% 2.11/0.67  fof(f617,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k1_xboole_0)))) )),
% 2.11/0.67    inference(resolution,[],[f599,f66])).
% 2.11/0.67  fof(f599,plain,(
% 2.11/0.67    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.11/0.67    inference(resolution,[],[f576,f139])).
% 2.11/0.67  fof(f139,plain,(
% 2.11/0.67    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.11/0.67    inference(resolution,[],[f138,f41])).
% 2.11/0.67  fof(f138,plain,(
% 2.11/0.67    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X1,X0),X0) | r1_tarski(X1,X0)) )),
% 2.11/0.67    inference(superposition,[],[f68,f60])).
% 2.11/0.67  fof(f68,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f54,f43])).
% 2.11/0.67  fof(f54,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f28])).
% 2.11/0.67  fof(f28,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.11/0.67    inference(ennf_transformation,[],[f11])).
% 2.11/0.67  fof(f11,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.11/0.67  fof(f576,plain,(
% 2.11/0.67    ( ! [X4,X5] : (~r1_tarski(X4,X5) | r1_xboole_0(X4,k1_xboole_0)) )),
% 2.11/0.67    inference(resolution,[],[f531,f67])).
% 2.11/0.67  fof(f67,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(definition_unfolding,[],[f51,f43])).
% 2.11/0.67  fof(f51,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.11/0.67    inference(cnf_transformation,[],[f26])).
% 2.11/0.67  fof(f26,plain,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.11/0.67    inference(ennf_transformation,[],[f4])).
% 2.11/0.67  fof(f4,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.11/0.67  fof(f531,plain,(
% 2.11/0.67    ( ! [X4,X5] : (~r1_tarski(X5,k5_xboole_0(k1_xboole_0,X4)) | r1_xboole_0(X5,k1_xboole_0)) )),
% 2.11/0.67    inference(superposition,[],[f56,f498])).
% 2.11/0.67  fof(f56,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k5_xboole_0(X1,X2))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f33])).
% 2.11/0.67  fof(f33,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.11/0.67    inference(flattening,[],[f32])).
% 2.11/0.67  fof(f32,plain,(
% 2.11/0.67    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 2.11/0.67    inference(nnf_transformation,[],[f3])).
% 2.11/0.67  fof(f3,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_xboole_1)).
% 2.11/0.67  fof(f808,plain,(
% 2.11/0.67    ( ! [X17,X16] : (k3_xboole_0(X16,k5_xboole_0(k1_xboole_0,k4_xboole_0(X17,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X16,X17),k1_xboole_0))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f786,f199])).
% 2.11/0.67  fof(f199,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(k3_xboole_0(X0,X1),k1_xboole_0)) )),
% 2.11/0.67    inference(superposition,[],[f46,f38])).
% 2.11/0.67  fof(f786,plain,(
% 2.11/0.67    ( ! [X17,X16] : (k3_xboole_0(X16,k5_xboole_0(k1_xboole_0,k4_xboole_0(X17,k1_xboole_0))) = k5_xboole_0(k1_xboole_0,k3_xboole_0(X16,k4_xboole_0(X17,k1_xboole_0)))) )),
% 2.11/0.67    inference(superposition,[],[f72,f38])).
% 2.11/0.67  fof(f927,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k3_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f404,f894])).
% 2.11/0.67  fof(f404,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,k1_xboole_0))) )),
% 2.11/0.67    inference(superposition,[],[f64,f74])).
% 2.11/0.67  fof(f64,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f48,f43])).
% 2.11/0.67  fof(f48,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f13])).
% 2.11/0.67  fof(f13,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 2.11/0.67  fof(f282,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(k4_xboole_0(X0,X1),X1))) )),
% 2.11/0.67    inference(superposition,[],[f215,f89])).
% 2.11/0.67  fof(f215,plain,(
% 2.11/0.67    ( ! [X47,X48,X49] : (r1_xboole_0(k3_xboole_0(X47,k4_xboole_0(X48,X49)),k3_xboole_0(X47,X49))) )),
% 2.11/0.67    inference(superposition,[],[f147,f46])).
% 2.11/0.67  fof(f147,plain,(
% 2.11/0.67    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.11/0.67    inference(resolution,[],[f139,f53])).
% 2.11/0.67  fof(f1966,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f1960,f1693])).
% 2.11/0.67  fof(f1693,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 2.11/0.67    inference(backward_demodulation,[],[f64,f1692])).
% 2.11/0.67  fof(f1692,plain,(
% 2.11/0.67    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X5,X6),X7)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f1667,f1434])).
% 2.11/0.67  fof(f1434,plain,(
% 2.11/0.67    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k4_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f198,f1433])).
% 2.11/0.67  fof(f1433,plain,(
% 2.11/0.67    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k3_xboole_0(X6,k4_xboole_0(X6,X7))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f1432,f1325])).
% 2.11/0.67  fof(f1432,plain,(
% 2.11/0.67    ( ! [X6,X7] : (k3_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X6,k4_xboole_0(X7,k1_xboole_0))) )),
% 2.11/0.67    inference(forward_demodulation,[],[f1384,f1232])).
% 2.11/0.67  fof(f1384,plain,(
% 2.11/0.67    ( ! [X6,X7] : (k3_xboole_0(X6,k4_xboole_0(X6,X7)) = k4_xboole_0(X6,k5_xboole_0(k1_xboole_0,k4_xboole_0(X7,k1_xboole_0)))) )),
% 2.11/0.67    inference(superposition,[],[f64,f1325])).
% 2.11/0.67  fof(f198,plain,(
% 2.11/0.67    ( ! [X8,X7] : (k3_xboole_0(X7,k4_xboole_0(X7,X8)) = k4_xboole_0(X7,k3_xboole_0(X7,X8))) )),
% 2.11/0.67    inference(superposition,[],[f46,f89])).
% 2.11/0.67  fof(f1667,plain,(
% 2.11/0.67    ( ! [X6,X7,X5] : (k3_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X7)) = k4_xboole_0(k4_xboole_0(X5,X6),k3_xboole_0(k4_xboole_0(X5,X6),X7))) )),
% 2.11/0.67    inference(superposition,[],[f46,f1339])).
% 2.11/0.67  fof(f1960,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f1351,f1903])).
% 2.11/0.67  fof(f1903,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f1693,f60])).
% 2.11/0.67  fof(f1351,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X6))) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f402,f1339])).
% 2.11/0.67  fof(f402,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k4_xboole_0(k3_xboole_0(k4_xboole_0(X5,X6),X5),k4_xboole_0(X5,X6)) = k4_xboole_0(X5,k5_xboole_0(X6,k4_xboole_0(k4_xboole_0(X5,X6),X6)))) )),
% 2.11/0.67    inference(superposition,[],[f64,f202])).
% 2.11/0.67  fof(f2037,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),X1))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f1755,f2035])).
% 2.11/0.67  fof(f2035,plain,(
% 2.11/0.67    ( ! [X103,X101,X102] : (k4_xboole_0(k4_xboole_0(X103,X102),k4_xboole_0(X101,X102)) = k4_xboole_0(k4_xboole_0(X103,X102),X101)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f2031,f1693])).
% 2.11/0.67  fof(f2031,plain,(
% 2.11/0.67    ( ! [X103,X101,X102] : (k4_xboole_0(k4_xboole_0(X103,X102),k4_xboole_0(X101,X102)) = k4_xboole_0(X103,k5_xboole_0(X102,k4_xboole_0(X101,X102)))) )),
% 2.11/0.67    inference(superposition,[],[f1693,f1903])).
% 2.11/0.67  fof(f1755,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X1,X0)))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f848,f1693])).
% 2.11/0.67  fof(f848,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(X1,X0)))) )),
% 2.11/0.67    inference(superposition,[],[f65,f60])).
% 2.11/0.67  fof(f65,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))),k4_xboole_0(k4_xboole_0(X1,k5_xboole_0(X0,k4_xboole_0(X2,X0))),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))))) )),
% 2.11/0.67    inference(definition_unfolding,[],[f49,f43,f43,f43])).
% 2.11/0.67  fof(f49,plain,(
% 2.11/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 2.11/0.67    inference(cnf_transformation,[],[f17])).
% 2.11/0.67  fof(f17,axiom,(
% 2.11/0.67    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 2.11/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).
% 2.11/0.67  fof(f5008,plain,(
% 2.11/0.67    sK2 != k4_xboole_0(k5_xboole_0(sK2,k2_enumset1(sK0,sK0,sK0,sK1)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.11/0.67    inference(backward_demodulation,[],[f59,f4911])).
% 2.11/0.67  fof(f4911,plain,(
% 2.11/0.67    k2_enumset1(sK0,sK0,sK0,sK1) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 2.11/0.67    inference(superposition,[],[f4559,f998])).
% 2.11/0.67  fof(f4559,plain,(
% 2.11/0.67    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = X1) )),
% 2.11/0.67    inference(forward_demodulation,[],[f4531,f1325])).
% 2.11/0.67  fof(f4531,plain,(
% 2.11/0.67    ( ! [X2,X1] : (k4_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f2042,f4438])).
% 2.11/0.67  fof(f4438,plain,(
% 2.11/0.67    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X3),X2)) )),
% 2.11/0.67    inference(superposition,[],[f3827,f1903])).
% 2.11/0.67  fof(f3827,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),X0)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f3768,f3222])).
% 2.11/0.67  fof(f3768,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X0),X0)) )),
% 2.11/0.67    inference(superposition,[],[f3299,f803])).
% 2.11/0.67  fof(f3299,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k4_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.11/0.67    inference(forward_demodulation,[],[f3291,f1232])).
% 2.11/0.67  fof(f3291,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,X0))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f2140,f3282])).
% 2.11/0.67  fof(f2140,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X1,X0))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f2036,f2133])).
% 2.11/0.67  fof(f2133,plain,(
% 2.11/0.67    ( ! [X19,X17,X18] : (k4_xboole_0(X19,X17) = k4_xboole_0(k4_xboole_0(X19,X17),k4_xboole_0(X17,X18))) )),
% 2.11/0.67    inference(superposition,[],[f1693,f1446])).
% 2.11/0.67  fof(f1446,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,X6),X5)) = X5) )),
% 2.11/0.67    inference(backward_demodulation,[],[f873,f1434])).
% 2.11/0.67  fof(f873,plain,(
% 2.11/0.67    ( ! [X6,X5] : (k5_xboole_0(X5,k4_xboole_0(k4_xboole_0(X5,k3_xboole_0(X5,X6)),X5)) = X5) )),
% 2.11/0.67    inference(superposition,[],[f803,f198])).
% 2.11/0.67  fof(f2036,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,X1)))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f1756,f2035])).
% 2.11/0.67  fof(f1756,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) )),
% 2.11/0.67    inference(backward_demodulation,[],[f838,f1693])).
% 2.11/0.67  fof(f838,plain,(
% 2.11/0.67    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))))) )),
% 2.11/0.67    inference(superposition,[],[f65,f60])).
% 2.11/0.67  fof(f2042,plain,(
% 2.11/0.67    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(X1,k4_xboole_0(k3_xboole_0(X1,X2),X1))) )),
% 2.11/0.67    inference(superposition,[],[f1434,f202])).
% 2.11/0.67  fof(f59,plain,(
% 2.11/0.67    sK2 != k4_xboole_0(k5_xboole_0(sK2,k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),k2_enumset1(sK0,sK0,sK0,sK1))),
% 2.11/0.67    inference(definition_unfolding,[],[f36,f43,f44,f44])).
% 2.11/0.67  fof(f36,plain,(
% 2.11/0.67    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.11/0.67    inference(cnf_transformation,[],[f31])).
% 2.11/0.67  % SZS output end Proof for theBenchmark
% 2.11/0.67  % (10773)------------------------------
% 2.11/0.67  % (10773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.67  % (10773)Termination reason: Refutation
% 2.11/0.67  
% 2.11/0.67  % (10773)Memory used [KB]: 4477
% 2.11/0.67  % (10773)Time elapsed: 0.240 s
% 2.11/0.67  % (10773)------------------------------
% 2.11/0.67  % (10773)------------------------------
% 2.11/0.67  % (10771)Success in time 0.31 s
%------------------------------------------------------------------------------
