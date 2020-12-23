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
% DateTime   : Thu Dec  3 12:42:29 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  114 (3550 expanded)
%              Number of leaves         :   12 ( 949 expanded)
%              Depth                    :   33
%              Number of atoms          :  196 (8764 expanded)
%              Number of equality atoms :  114 (6193 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5768,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5760,f4403])).

fof(f4403,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f2945,f4162])).

fof(f4162,plain,(
    sK0 != sK2 ),
    inference(subsumption_resolution,[],[f25,f4161])).

fof(f4161,plain,(
    sK1 = sK3 ),
    inference(global_subsumption,[],[f3473,f4158])).

fof(f4158,plain,(
    r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f4113,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f4113,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f3170,f4066])).

fof(f4066,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f4065,f22])).

fof(f22,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f4065,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f4008,f2947])).

fof(f2947,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f2944,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2944,plain,(
    r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f2940,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f2940,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f2886,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f2886,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f159,f2698])).

fof(f2698,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f2618,f2697])).

fof(f2697,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f2694,f570])).

fof(f570,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f565,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f565,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f504,f22])).

fof(f504,plain,(
    ! [X28,X26,X27] : r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X26,X27)),k2_zfmisc_1(X28,X26)) ),
    inference(superposition,[],[f473,f90])).

fof(f90,plain,(
    ! [X6,X5] : k2_xboole_0(k3_xboole_0(X5,X6),X5) = X5 ),
    inference(resolution,[],[f31,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f42,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f473,plain,(
    ! [X6,X4,X5] : r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_xboole_0(X5,X6))) ),
    inference(superposition,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f2694,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))
    | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f2690,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2690,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f2683,f22])).

fof(f2683,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f2662,f58])).

fof(f58,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f30,f40])).

fof(f2662,plain,(
    ! [X24] : r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X24)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f2661,f1802])).

fof(f1802,plain,(
    ! [X27] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X27)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X27)) ),
    inference(superposition,[],[f813,f22])).

fof(f813,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) ),
    inference(superposition,[],[f39,f58])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f2661,plain,(
    ! [X24] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X24)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f2649,f39])).

fof(f2649,plain,(
    ! [X24] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X24)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f504,f2618])).

fof(f2618,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2617,f27])).

fof(f2617,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f2587,f27])).

fof(f2587,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f1802,f1738])).

fof(f1738,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X2,X1),X0) ),
    inference(superposition,[],[f814,f58])).

fof(f814,plain,(
    ! [X6,X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6)) ),
    inference(superposition,[],[f39,f27])).

fof(f159,plain,(
    ! [X21,X22,X20] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X20,X21),X22),k2_zfmisc_1(X21,X22)) ),
    inference(superposition,[],[f133,f91])).

fof(f91,plain,(
    ! [X8,X7] : k2_xboole_0(k3_xboole_0(X7,X8),X8) = X8 ),
    inference(resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f48,f27])).

fof(f133,plain,(
    ! [X17,X15,X16] : r1_tarski(k2_zfmisc_1(X15,X16),k2_zfmisc_1(k2_xboole_0(X15,X17),X16)) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f4008,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(superposition,[],[f2999,f58])).

fof(f2999,plain,(
    ! [X28] : k2_zfmisc_1(k3_xboole_0(sK0,X28),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,X28),sK3) ),
    inference(backward_demodulation,[],[f1905,f2946])).

fof(f2946,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f2944,f31])).

fof(f1905,plain,(
    ! [X28] : k2_zfmisc_1(k3_xboole_0(k2_xboole_0(sK0,sK2),X28),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X28),sK3) ),
    inference(forward_demodulation,[],[f1861,f834])).

fof(f834,plain,(
    ! [X39,X41,X42,X40] : k3_xboole_0(k2_zfmisc_1(X41,k2_xboole_0(X39,X40)),k2_zfmisc_1(X42,X40)) = k2_zfmisc_1(k3_xboole_0(X41,X42),X40) ),
    inference(superposition,[],[f39,f355])).

fof(f355,plain,(
    ! [X8,X7] : k3_xboole_0(k2_xboole_0(X8,X7),X7) = X7 ),
    inference(superposition,[],[f288,f60])).

fof(f60,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3 ),
    inference(resolution,[],[f30,f42])).

fof(f288,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f62,f27])).

fof(f62,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),X8) ),
    inference(resolution,[],[f30,f50])).

fof(f1861,plain,(
    ! [X28] : k2_zfmisc_1(k3_xboole_0(k2_xboole_0(sK0,sK2),X28),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X28,sK3)) ),
    inference(superposition,[],[f824,f668])).

fof(f668,plain,(
    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f644,f28])).

fof(f644,plain,(
    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f123,f36])).

fof(f123,plain,(
    ! [X0] : k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f35,f22])).

fof(f824,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f39,f58])).

fof(f3170,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X6))
      | r1_tarski(sK1,X6) ) ),
    inference(forward_demodulation,[],[f3169,f2947])).

fof(f3169,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))
      | r1_tarski(sK1,X6) ) ),
    inference(subsumption_resolution,[],[f3154,f23])).

fof(f23,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f3154,plain,(
    ! [X6] :
      ( k1_xboole_0 = sK0
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))
      | r1_tarski(sK1,X6) ) ),
    inference(backward_demodulation,[],[f2704,f2947])).

fof(f2704,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))
      | r1_tarski(sK1,X6)
      | k1_xboole_0 = k3_xboole_0(sK0,sK2) ) ),
    inference(backward_demodulation,[],[f2633,f2697])).

fof(f2633,plain,(
    ! [X6] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6))
      | r1_tarski(sK1,X6)
      | k1_xboole_0 = k3_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f38,f2618])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3473,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f3472,f34])).

fof(f3472,plain,(
    r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f3468,f23])).

fof(f3468,plain,
    ( r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f3454,f38])).

fof(f3454,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f3207,f22])).

fof(f3207,plain,(
    ! [X4] : r1_tarski(k2_zfmisc_1(sK0,X4),k2_zfmisc_1(sK2,X4)) ),
    inference(superposition,[],[f133,f2946])).

fof(f25,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f19])).

fof(f2945,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(resolution,[],[f2944,f34])).

fof(f5760,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f4404,f40])).

fof(f4404,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK1))
      | r1_tarski(sK2,X4) ) ),
    inference(backward_demodulation,[],[f3079,f4163])).

fof(f4163,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(backward_demodulation,[],[f22,f4161])).

fof(f3079,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X4,sK1))
      | r1_tarski(sK2,X4) ) ),
    inference(forward_demodulation,[],[f2972,f2961])).

fof(f2961,plain,(
    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f751,f2946])).

fof(f751,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f729,f28])).

fof(f729,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f465,f35])).

fof(f465,plain,(
    ! [X0] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0)) ),
    inference(superposition,[],[f36,f22])).

fof(f2972,plain,(
    ! [X4] :
      ( r1_tarski(sK2,X4)
      | ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1)) ) ),
    inference(backward_demodulation,[],[f772,f2946])).

fof(f772,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1))
      | r1_tarski(k2_xboole_0(sK0,sK2),X4) ) ),
    inference(subsumption_resolution,[],[f760,f24])).

fof(f760,plain,(
    ! [X4] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1))
      | r1_tarski(k2_xboole_0(sK0,sK2),X4)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f37,f751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (15425)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.48  % (15415)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.49  % (15405)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.49  % (15406)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.49  % (15427)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.50  % (15400)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (15412)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.50  % (15419)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (15404)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (15411)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.50  % (15414)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (15401)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (15424)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.51  % (15422)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.51  % (15403)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.51  % (15413)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (15416)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.52  % (15402)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.52  % (15408)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.52  % (15420)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.52  % (15410)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.52  % (15421)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.53  % (15417)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.53  % (15426)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.53  % (15409)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.55  % (15407)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 4.27/0.90  % (15400)Time limit reached!
% 4.27/0.90  % (15400)------------------------------
% 4.27/0.90  % (15400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.27/0.91  % (15400)Termination reason: Time limit
% 4.27/0.91  
% 4.27/0.91  % (15400)Memory used [KB]: 14456
% 4.27/0.91  % (15400)Time elapsed: 0.504 s
% 4.27/0.91  % (15400)------------------------------
% 4.27/0.91  % (15400)------------------------------
% 4.47/0.93  % (15414)Time limit reached!
% 4.47/0.93  % (15414)------------------------------
% 4.47/0.93  % (15414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/0.93  % (15414)Termination reason: Time limit
% 4.47/0.93  % (15414)Termination phase: Saturation
% 4.47/0.93  
% 4.47/0.93  % (15414)Memory used [KB]: 10618
% 4.47/0.93  % (15414)Time elapsed: 0.500 s
% 4.47/0.93  % (15414)------------------------------
% 4.47/0.93  % (15414)------------------------------
% 4.47/0.97  % (15413)Time limit reached!
% 4.47/0.97  % (15413)------------------------------
% 4.47/0.97  % (15413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/0.98  % (15413)Termination reason: Time limit
% 4.47/0.98  
% 4.47/0.98  % (15413)Memory used [KB]: 10362
% 4.47/0.98  % (15413)Time elapsed: 0.575 s
% 4.47/0.98  % (15413)------------------------------
% 4.47/0.98  % (15413)------------------------------
% 4.47/0.98  % (15403)Refutation found. Thanks to Tanya!
% 4.47/0.98  % SZS status Theorem for theBenchmark
% 4.47/0.98  % SZS output start Proof for theBenchmark
% 4.47/0.98  fof(f5768,plain,(
% 4.47/0.98    $false),
% 4.47/0.98    inference(subsumption_resolution,[],[f5760,f4403])).
% 4.47/0.98  fof(f4403,plain,(
% 4.47/0.98    ~r1_tarski(sK2,sK0)),
% 4.47/0.98    inference(subsumption_resolution,[],[f2945,f4162])).
% 4.47/0.98  fof(f4162,plain,(
% 4.47/0.98    sK0 != sK2),
% 4.47/0.98    inference(subsumption_resolution,[],[f25,f4161])).
% 4.47/0.98  fof(f4161,plain,(
% 4.47/0.98    sK1 = sK3),
% 4.47/0.98    inference(global_subsumption,[],[f3473,f4158])).
% 4.47/0.98  fof(f4158,plain,(
% 4.47/0.98    r1_tarski(sK1,sK3)),
% 4.47/0.98    inference(subsumption_resolution,[],[f4113,f40])).
% 4.47/0.98  fof(f40,plain,(
% 4.47/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.47/0.98    inference(equality_resolution,[],[f33])).
% 4.47/0.98  fof(f33,plain,(
% 4.47/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.47/0.98    inference(cnf_transformation,[],[f21])).
% 4.47/0.98  fof(f21,plain,(
% 4.47/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.47/0.98    inference(flattening,[],[f20])).
% 4.47/0.98  fof(f20,plain,(
% 4.47/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.47/0.98    inference(nnf_transformation,[],[f3])).
% 4.47/0.98  fof(f3,axiom,(
% 4.47/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.47/0.98  fof(f4113,plain,(
% 4.47/0.98    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK1,sK3)),
% 4.47/0.98    inference(superposition,[],[f3170,f4066])).
% 4.47/0.98  fof(f4066,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 4.47/0.98    inference(forward_demodulation,[],[f4065,f22])).
% 4.47/0.98  fof(f22,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 4.47/0.98    inference(cnf_transformation,[],[f19])).
% 4.47/0.98  fof(f19,plain,(
% 4.47/0.98    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 4.47/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f18])).
% 4.47/0.98  fof(f18,plain,(
% 4.47/0.98    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 4.47/0.98    introduced(choice_axiom,[])).
% 4.47/0.98  fof(f14,plain,(
% 4.47/0.98    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 4.47/0.98    inference(flattening,[],[f13])).
% 4.47/0.98  fof(f13,plain,(
% 4.47/0.98    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 4.47/0.98    inference(ennf_transformation,[],[f12])).
% 4.47/0.98  fof(f12,negated_conjecture,(
% 4.47/0.98    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.47/0.98    inference(negated_conjecture,[],[f11])).
% 4.47/0.98  fof(f11,conjecture,(
% 4.47/0.98    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 4.47/0.98  fof(f4065,plain,(
% 4.47/0.98    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,sK3)),
% 4.47/0.98    inference(forward_demodulation,[],[f4008,f2947])).
% 4.47/0.98  fof(f2947,plain,(
% 4.47/0.98    sK0 = k3_xboole_0(sK0,sK2)),
% 4.47/0.98    inference(resolution,[],[f2944,f30])).
% 4.47/0.98  fof(f30,plain,(
% 4.47/0.98    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.47/0.98    inference(cnf_transformation,[],[f15])).
% 4.47/0.98  fof(f15,plain,(
% 4.47/0.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.47/0.98    inference(ennf_transformation,[],[f6])).
% 4.47/0.98  fof(f6,axiom,(
% 4.47/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.47/0.98  fof(f2944,plain,(
% 4.47/0.98    r1_tarski(sK0,sK2)),
% 4.47/0.98    inference(subsumption_resolution,[],[f2940,f24])).
% 4.47/0.98  fof(f24,plain,(
% 4.47/0.98    k1_xboole_0 != sK1),
% 4.47/0.98    inference(cnf_transformation,[],[f19])).
% 4.47/0.98  fof(f2940,plain,(
% 4.47/0.98    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 4.47/0.98    inference(resolution,[],[f2886,f37])).
% 4.47/0.98  fof(f37,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 4.47/0.98    inference(cnf_transformation,[],[f17])).
% 4.47/0.98  fof(f17,plain,(
% 4.47/0.98    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 4.47/0.98    inference(ennf_transformation,[],[f8])).
% 4.47/0.98  fof(f8,axiom,(
% 4.47/0.98    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 4.47/0.98  fof(f2886,plain,(
% 4.47/0.98    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 4.47/0.98    inference(superposition,[],[f159,f2698])).
% 4.47/0.98  fof(f2698,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1)),
% 4.47/0.98    inference(backward_demodulation,[],[f2618,f2697])).
% 4.47/0.98  fof(f2697,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 4.47/0.98    inference(subsumption_resolution,[],[f2694,f570])).
% 4.47/0.98  fof(f570,plain,(
% 4.47/0.98    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(X0,sK3)),k2_zfmisc_1(sK0,sK1))) )),
% 4.47/0.98    inference(superposition,[],[f565,f27])).
% 4.47/0.98  fof(f27,plain,(
% 4.47/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.47/0.98    inference(cnf_transformation,[],[f2])).
% 4.47/0.98  fof(f2,axiom,(
% 4.47/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.47/0.98  fof(f565,plain,(
% 4.47/0.98    ( ! [X0] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X0)),k2_zfmisc_1(sK0,sK1))) )),
% 4.47/0.98    inference(superposition,[],[f504,f22])).
% 4.47/0.98  fof(f504,plain,(
% 4.47/0.98    ( ! [X28,X26,X27] : (r1_tarski(k2_zfmisc_1(X28,k3_xboole_0(X26,X27)),k2_zfmisc_1(X28,X26))) )),
% 4.47/0.98    inference(superposition,[],[f473,f90])).
% 4.47/0.98  fof(f90,plain,(
% 4.47/0.98    ( ! [X6,X5] : (k2_xboole_0(k3_xboole_0(X5,X6),X5) = X5) )),
% 4.47/0.98    inference(resolution,[],[f31,f48])).
% 4.47/0.98  fof(f48,plain,(
% 4.47/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.47/0.98    inference(superposition,[],[f42,f29])).
% 4.47/0.98  fof(f29,plain,(
% 4.47/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 4.47/0.98    inference(cnf_transformation,[],[f5])).
% 4.47/0.98  fof(f5,axiom,(
% 4.47/0.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 4.47/0.98  fof(f42,plain,(
% 4.47/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 4.47/0.98    inference(superposition,[],[f26,f28])).
% 4.47/0.98  fof(f28,plain,(
% 4.47/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.47/0.98    inference(cnf_transformation,[],[f1])).
% 4.47/0.98  fof(f1,axiom,(
% 4.47/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.47/0.98  fof(f26,plain,(
% 4.47/0.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.47/0.98    inference(cnf_transformation,[],[f7])).
% 4.47/0.98  fof(f7,axiom,(
% 4.47/0.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.47/0.98  fof(f31,plain,(
% 4.47/0.98    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.47/0.98    inference(cnf_transformation,[],[f16])).
% 4.47/0.98  fof(f16,plain,(
% 4.47/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.47/0.98    inference(ennf_transformation,[],[f4])).
% 4.47/0.98  fof(f4,axiom,(
% 4.47/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.47/0.98  fof(f473,plain,(
% 4.47/0.98    ( ! [X6,X4,X5] : (r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,k2_xboole_0(X5,X6)))) )),
% 4.47/0.98    inference(superposition,[],[f26,f36])).
% 4.47/0.98  fof(f36,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.47/0.98    inference(cnf_transformation,[],[f9])).
% 4.47/0.98  fof(f9,axiom,(
% 4.47/0.98    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 4.47/0.98  fof(f2694,plain,(
% 4.47/0.98    ~r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) | k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 4.47/0.98    inference(resolution,[],[f2690,f34])).
% 4.47/0.98  fof(f34,plain,(
% 4.47/0.98    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 4.47/0.98    inference(cnf_transformation,[],[f21])).
% 4.47/0.98  fof(f2690,plain,(
% 4.47/0.98    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 4.47/0.98    inference(forward_demodulation,[],[f2683,f22])).
% 4.47/0.98  fof(f2683,plain,(
% 4.47/0.98    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))),
% 4.47/0.98    inference(superposition,[],[f2662,f58])).
% 4.47/0.98  fof(f58,plain,(
% 4.47/0.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.47/0.98    inference(resolution,[],[f30,f40])).
% 4.47/0.98  fof(f2662,plain,(
% 4.47/0.98    ( ! [X24] : (r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK3,X24)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) )),
% 4.47/0.98    inference(forward_demodulation,[],[f2661,f1802])).
% 4.47/0.98  fof(f1802,plain,(
% 4.47/0.98    ( ! [X27] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X27)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X27))) )),
% 4.47/0.98    inference(superposition,[],[f813,f22])).
% 4.47/0.98  fof(f813,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))) )),
% 4.47/0.98    inference(superposition,[],[f39,f58])).
% 4.47/0.98  fof(f39,plain,(
% 4.47/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 4.47/0.98    inference(cnf_transformation,[],[f10])).
% 4.47/0.98  fof(f10,axiom,(
% 4.47/0.98    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 4.47/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 4.47/0.98  fof(f2661,plain,(
% 4.47/0.98    ( ! [X24] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X24)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) )),
% 4.47/0.98    inference(forward_demodulation,[],[f2649,f39])).
% 4.47/0.98  fof(f2649,plain,(
% 4.47/0.98    ( ! [X24] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X24)),k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)))) )),
% 4.47/0.98    inference(superposition,[],[f504,f2618])).
% 4.47/0.98  fof(f2618,plain,(
% 4.47/0.98    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 4.47/0.98    inference(forward_demodulation,[],[f2617,f27])).
% 4.47/0.98  fof(f2617,plain,(
% 4.47/0.98    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 4.47/0.98    inference(forward_demodulation,[],[f2587,f27])).
% 4.47/0.98  fof(f2587,plain,(
% 4.47/0.98    k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK1))),
% 4.47/0.98    inference(superposition,[],[f1802,f1738])).
% 4.47/0.98  fof(f1738,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X2,X1),X0)) )),
% 4.47/0.98    inference(superposition,[],[f814,f58])).
% 4.47/0.98  fof(f814,plain,(
% 4.47/0.98    ( ! [X6,X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X6)) = k2_zfmisc_1(k3_xboole_0(X4,X3),k3_xboole_0(X5,X6))) )),
% 4.47/0.98    inference(superposition,[],[f39,f27])).
% 4.47/0.98  fof(f159,plain,(
% 4.47/0.98    ( ! [X21,X22,X20] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X20,X21),X22),k2_zfmisc_1(X21,X22))) )),
% 4.47/0.98    inference(superposition,[],[f133,f91])).
% 4.47/0.98  fof(f91,plain,(
% 4.47/0.98    ( ! [X8,X7] : (k2_xboole_0(k3_xboole_0(X7,X8),X8) = X8) )),
% 4.47/0.98    inference(resolution,[],[f31,f50])).
% 4.47/0.98  fof(f50,plain,(
% 4.47/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 4.47/0.98    inference(superposition,[],[f48,f27])).
% 4.47/0.98  fof(f133,plain,(
% 4.47/0.98    ( ! [X17,X15,X16] : (r1_tarski(k2_zfmisc_1(X15,X16),k2_zfmisc_1(k2_xboole_0(X15,X17),X16))) )),
% 4.47/0.98    inference(superposition,[],[f26,f35])).
% 4.47/0.98  fof(f35,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 4.47/0.98    inference(cnf_transformation,[],[f9])).
% 4.47/0.98  fof(f4008,plain,(
% 4.47/0.98    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 4.47/0.98    inference(superposition,[],[f2999,f58])).
% 4.47/0.98  fof(f2999,plain,(
% 4.47/0.98    ( ! [X28] : (k2_zfmisc_1(k3_xboole_0(sK0,X28),sK3) = k2_zfmisc_1(k3_xboole_0(sK2,X28),sK3)) )),
% 4.47/0.98    inference(backward_demodulation,[],[f1905,f2946])).
% 4.47/0.98  fof(f2946,plain,(
% 4.47/0.98    sK2 = k2_xboole_0(sK0,sK2)),
% 4.47/0.98    inference(resolution,[],[f2944,f31])).
% 4.47/0.98  fof(f1905,plain,(
% 4.47/0.98    ( ! [X28] : (k2_zfmisc_1(k3_xboole_0(k2_xboole_0(sK0,sK2),X28),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X28),sK3)) )),
% 4.47/0.98    inference(forward_demodulation,[],[f1861,f834])).
% 4.47/0.98  fof(f834,plain,(
% 4.47/0.98    ( ! [X39,X41,X42,X40] : (k3_xboole_0(k2_zfmisc_1(X41,k2_xboole_0(X39,X40)),k2_zfmisc_1(X42,X40)) = k2_zfmisc_1(k3_xboole_0(X41,X42),X40)) )),
% 4.47/0.98    inference(superposition,[],[f39,f355])).
% 4.47/0.98  fof(f355,plain,(
% 4.47/0.98    ( ! [X8,X7] : (k3_xboole_0(k2_xboole_0(X8,X7),X7) = X7) )),
% 4.47/0.98    inference(superposition,[],[f288,f60])).
% 4.47/0.98  fof(f60,plain,(
% 4.47/0.98    ( ! [X4,X3] : (k3_xboole_0(X3,k2_xboole_0(X4,X3)) = X3) )),
% 4.47/0.98    inference(resolution,[],[f30,f42])).
% 4.47/0.98  fof(f288,plain,(
% 4.47/0.98    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 4.47/0.98    inference(superposition,[],[f62,f27])).
% 4.47/0.98  fof(f62,plain,(
% 4.47/0.98    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),X8)) )),
% 4.47/0.98    inference(resolution,[],[f30,f50])).
% 4.47/0.98  fof(f1861,plain,(
% 4.47/0.98    ( ! [X28] : (k2_zfmisc_1(k3_xboole_0(k2_xboole_0(sK0,sK2),X28),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X28,sK3))) )),
% 4.47/0.98    inference(superposition,[],[f824,f668])).
% 4.47/0.98  fof(f668,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3)),
% 4.47/0.98    inference(forward_demodulation,[],[f644,f28])).
% 4.47/0.98  fof(f644,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK2,sK0),sK3)),
% 4.47/0.98    inference(superposition,[],[f123,f36])).
% 4.47/0.98  fof(f123,plain,(
% 4.47/0.98    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 4.47/0.98    inference(superposition,[],[f35,f22])).
% 4.47/0.98  fof(f824,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 4.47/0.98    inference(superposition,[],[f39,f58])).
% 4.47/0.98  fof(f3170,plain,(
% 4.47/0.98    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X6)) | r1_tarski(sK1,X6)) )),
% 4.47/0.98    inference(forward_demodulation,[],[f3169,f2947])).
% 4.47/0.98  fof(f3169,plain,(
% 4.47/0.98    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6)) | r1_tarski(sK1,X6)) )),
% 4.47/0.98    inference(subsumption_resolution,[],[f3154,f23])).
% 4.47/0.98  fof(f23,plain,(
% 4.47/0.98    k1_xboole_0 != sK0),
% 4.47/0.98    inference(cnf_transformation,[],[f19])).
% 4.47/0.98  fof(f3154,plain,(
% 4.47/0.98    ( ! [X6] : (k1_xboole_0 = sK0 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6)) | r1_tarski(sK1,X6)) )),
% 4.47/0.98    inference(backward_demodulation,[],[f2704,f2947])).
% 4.47/0.98  fof(f2704,plain,(
% 4.47/0.98    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6)) | r1_tarski(sK1,X6) | k1_xboole_0 = k3_xboole_0(sK0,sK2)) )),
% 4.47/0.98    inference(backward_demodulation,[],[f2633,f2697])).
% 4.47/0.98  fof(f2633,plain,(
% 4.47/0.98    ( ! [X6] : (~r1_tarski(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X6)) | r1_tarski(sK1,X6) | k1_xboole_0 = k3_xboole_0(sK0,sK2)) )),
% 4.47/0.98    inference(superposition,[],[f38,f2618])).
% 4.47/0.98  fof(f38,plain,(
% 4.47/0.98    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 4.47/0.98    inference(cnf_transformation,[],[f17])).
% 4.47/0.98  fof(f3473,plain,(
% 4.47/0.98    ~r1_tarski(sK1,sK3) | sK1 = sK3),
% 4.47/0.98    inference(resolution,[],[f3472,f34])).
% 4.47/0.98  fof(f3472,plain,(
% 4.47/0.98    r1_tarski(sK3,sK1)),
% 4.47/0.98    inference(subsumption_resolution,[],[f3468,f23])).
% 4.47/0.98  fof(f3468,plain,(
% 4.47/0.98    r1_tarski(sK3,sK1) | k1_xboole_0 = sK0),
% 4.47/0.98    inference(resolution,[],[f3454,f38])).
% 4.47/0.98  fof(f3454,plain,(
% 4.47/0.98    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK1))),
% 4.47/0.98    inference(superposition,[],[f3207,f22])).
% 4.47/0.98  fof(f3207,plain,(
% 4.47/0.98    ( ! [X4] : (r1_tarski(k2_zfmisc_1(sK0,X4),k2_zfmisc_1(sK2,X4))) )),
% 4.47/0.98    inference(superposition,[],[f133,f2946])).
% 4.47/0.98  fof(f25,plain,(
% 4.47/0.98    sK1 != sK3 | sK0 != sK2),
% 4.47/0.98    inference(cnf_transformation,[],[f19])).
% 4.47/0.98  fof(f2945,plain,(
% 4.47/0.98    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 4.47/0.98    inference(resolution,[],[f2944,f34])).
% 4.47/0.98  fof(f5760,plain,(
% 4.47/0.98    r1_tarski(sK2,sK0)),
% 4.47/0.98    inference(resolution,[],[f4404,f40])).
% 4.47/0.98  fof(f4404,plain,(
% 4.47/0.98    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK1)) | r1_tarski(sK2,X4)) )),
% 4.47/0.98    inference(backward_demodulation,[],[f3079,f4163])).
% 4.47/0.98  fof(f4163,plain,(
% 4.47/0.98    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 4.47/0.98    inference(backward_demodulation,[],[f22,f4161])).
% 4.47/0.98  fof(f3079,plain,(
% 4.47/0.98    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(X4,sK1)) | r1_tarski(sK2,X4)) )),
% 4.47/0.98    inference(forward_demodulation,[],[f2972,f2961])).
% 4.47/0.98  fof(f2961,plain,(
% 4.47/0.98    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))),
% 4.47/0.98    inference(backward_demodulation,[],[f751,f2946])).
% 4.47/0.98  fof(f751,plain,(
% 4.47/0.98    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))),
% 4.47/0.98    inference(forward_demodulation,[],[f729,f28])).
% 4.47/0.98  fof(f729,plain,(
% 4.47/0.98    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1))),
% 4.47/0.98    inference(superposition,[],[f465,f35])).
% 4.47/0.98  fof(f465,plain,(
% 4.47/0.98    ( ! [X0] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X0))) )),
% 4.47/0.98    inference(superposition,[],[f36,f22])).
% 4.47/0.98  fof(f2972,plain,(
% 4.47/0.98    ( ! [X4] : (r1_tarski(sK2,X4) | ~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1))) )),
% 4.47/0.98    inference(backward_demodulation,[],[f772,f2946])).
% 4.47/0.98  fof(f772,plain,(
% 4.47/0.98    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X4)) )),
% 4.47/0.98    inference(subsumption_resolution,[],[f760,f24])).
% 4.47/0.98  fof(f760,plain,(
% 4.47/0.98    ( ! [X4] : (~r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)),k2_zfmisc_1(X4,sK1)) | r1_tarski(k2_xboole_0(sK0,sK2),X4) | k1_xboole_0 = sK1) )),
% 4.47/0.98    inference(superposition,[],[f37,f751])).
% 4.47/0.98  % SZS output end Proof for theBenchmark
% 4.47/0.98  % (15403)------------------------------
% 4.47/0.98  % (15403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.47/0.98  % (15403)Termination reason: Refutation
% 4.47/0.98  
% 4.47/0.98  % (15403)Memory used [KB]: 11129
% 4.47/0.98  % (15403)Time elapsed: 0.556 s
% 4.47/0.98  % (15403)------------------------------
% 4.47/0.98  % (15403)------------------------------
% 4.47/0.98  % (15395)Success in time 0.627 s
%------------------------------------------------------------------------------
