%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:56 EST 2020

% Result     : Theorem 2.62s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  119 (2009 expanded)
%              Number of leaves         :   13 ( 551 expanded)
%              Depth                    :   35
%              Number of atoms          :  172 (3854 expanded)
%              Number of equality atoms :  109 (2050 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3845,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3844,f3614])).

fof(f3614,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f3613,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3613,plain,(
    k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f3605,f25])).

fof(f25,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f3605,plain,
    ( k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f3598,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK0)
      | k2_xboole_0(X0,sK0) != k2_xboole_0(sK0,sK2)
      | sK2 = X0 ) ),
    inference(forward_demodulation,[],[f46,f29])).

fof(f46,plain,(
    ! [X0] :
      ( k2_xboole_0(X0,sK0) != k2_xboole_0(sK2,sK0)
      | ~ r1_xboole_0(X0,sK0)
      | sK2 = X0 ) ),
    inference(resolution,[],[f23,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X2,X1)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_xboole_0(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X2,X1)
        & r1_xboole_0(X0,X1)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1) )
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

fof(f23,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f3598,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f3559,f59])).

fof(f59,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f24,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f3559,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(X3,sK3)
      | r1_xboole_0(X3,sK0) ) ),
    inference(superposition,[],[f38,f3526])).

fof(f3526,plain,(
    sK3 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f3525,f28])).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f3525,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f3520,f29])).

fof(f3520,plain,(
    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0) ),
    inference(superposition,[],[f31,f3499])).

fof(f3499,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f3480,f1969])).

fof(f1969,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f1809,f1773])).

fof(f1773,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f1719,f100])).

fof(f100,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f43,f66])).

fof(f66,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f51,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f51,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f23,f33])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f1719,plain,(
    ! [X2] : k2_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(forward_demodulation,[],[f1703,f28])).

fof(f1703,plain,(
    ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f912,f29])).

fof(f912,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) ),
    inference(backward_demodulation,[],[f355,f908])).

fof(f908,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f898,f50])).

fof(f50,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f23,f44])).

fof(f898,plain,(
    k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f83,f89])).

fof(f89,plain,(
    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) ),
    inference(forward_demodulation,[],[f87,f28])).

fof(f87,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f31,f50])).

fof(f83,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f36,f50])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f355,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,sK2),X0)) ),
    inference(superposition,[],[f37,f324])).

fof(f324,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(superposition,[],[f43,f236])).

fof(f236,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(resolution,[],[f211,f44])).

fof(f211,plain,(
    r1_xboole_0(k1_xboole_0,sK2) ),
    inference(resolution,[],[f204,f33])).

fof(f204,plain,(
    r1_xboole_0(sK2,k1_xboole_0) ),
    inference(resolution,[],[f194,f23])).

fof(f194,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK0)
      | r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f38,f100])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1809,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) ),
    inference(backward_demodulation,[],[f101,f1770])).

fof(f1770,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f1719,f993])).

fof(f993,plain,(
    ! [X2] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f43,f954])).

fof(f954,plain,(
    ! [X8] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X8)) ),
    inference(resolution,[],[f916,f44])).

fof(f916,plain,(
    ! [X9] : r1_xboole_0(k1_xboole_0,X9) ),
    inference(backward_demodulation,[],[f854,f908])).

fof(f854,plain,(
    ! [X9] : r1_xboole_0(k4_xboole_0(k1_xboole_0,sK2),X9) ),
    inference(resolution,[],[f848,f33])).

fof(f848,plain,(
    ! [X4] : r1_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK2)) ),
    inference(subsumption_resolution,[],[f835,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f835,plain,(
    ! [X4] :
      ( r1_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK2))
      | k1_xboole_0 != k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0)) ) ),
    inference(resolution,[],[f357,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f357,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k1_xboole_0)
      | r1_xboole_0(X2,k4_xboole_0(k1_xboole_0,sK2)) ) ),
    inference(superposition,[],[f39,f324])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0)) ),
    inference(superposition,[],[f36,f66])).

fof(f3480,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2215,f22])).

fof(f22,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f2215,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f36,f1773])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3844,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f2369,f3841])).

fof(f3841,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f3840,f28])).

fof(f3840,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f3837,f29])).

fof(f3837,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f31,f3820])).

fof(f3820,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f3802,f2310])).

fof(f2310,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f2030,f29])).

fof(f2030,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(backward_demodulation,[],[f1810,f1775])).

fof(f1775,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f1719,f114])).

fof(f114,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f43,f72])).

fof(f72,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f59,f44])).

fof(f1810,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(backward_demodulation,[],[f115,f1770])).

fof(f115,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0)) ),
    inference(superposition,[],[f36,f72])).

fof(f3802,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2222,f2863])).

fof(f2863,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f2848,f2369])).

fof(f2848,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f2443,f80])).

fof(f80,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f74,f37])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f37,f22])).

fof(f2443,plain,(
    ! [X3] : k2_xboole_0(X3,sK2) = k2_xboole_0(sK2,k2_xboole_0(X3,sK2)) ),
    inference(superposition,[],[f2063,f29])).

fof(f2063,plain,(
    ! [X0] : k2_xboole_0(sK2,X0) = k2_xboole_0(sK2,k2_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f457,f1777])).

fof(f1777,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f1719,f82])).

fof(f82,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f43,f50])).

fof(f457,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK2,sK0),X0) = k2_xboole_0(k4_xboole_0(sK2,sK0),k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f37,f89])).

fof(f2222,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f36,f1775])).

fof(f2369,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f2368,f28])).

fof(f2368,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f2367,f1264])).

fof(f1264,plain,(
    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f278,f22])).

fof(f278,plain,(
    ! [X0] : k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f80,f29])).

fof(f2367,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2359,f29])).

fof(f2359,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(superposition,[],[f31,f2259])).

fof(f2259,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f2080,f22])).

fof(f2080,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) ),
    inference(backward_demodulation,[],[f1807,f1777])).

fof(f1807,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) ),
    inference(backward_demodulation,[],[f83,f1770])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:37:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (9511)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.48  % (9527)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.48  % (9518)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.49  % (9536)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.50  % (9528)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.50  % (9519)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (9514)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (9516)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (9513)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (9512)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (9528)Refutation not found, incomplete strategy% (9528)------------------------------
% 0.21/0.52  % (9528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (9528)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (9528)Memory used [KB]: 10618
% 0.21/0.52  % (9528)Time elapsed: 0.131 s
% 0.21/0.52  % (9528)------------------------------
% 0.21/0.52  % (9528)------------------------------
% 0.21/0.52  % (9515)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (9526)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (9531)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (9532)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (9535)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (9524)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (9523)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (9525)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (9538)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (9529)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (9540)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (9534)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (9517)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9539)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (9541)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (9537)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (9520)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (9530)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (9522)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (9533)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 2.06/0.64  % (9622)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.62/0.74  % (9529)Refutation found. Thanks to Tanya!
% 2.62/0.74  % SZS status Theorem for theBenchmark
% 2.62/0.74  % SZS output start Proof for theBenchmark
% 2.62/0.74  fof(f3845,plain,(
% 2.62/0.74    $false),
% 2.62/0.74    inference(subsumption_resolution,[],[f3844,f3614])).
% 2.62/0.74  fof(f3614,plain,(
% 2.62/0.74    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f3613,f29])).
% 2.62/0.74  fof(f29,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.62/0.74    inference(cnf_transformation,[],[f1])).
% 2.62/0.74  fof(f1,axiom,(
% 2.62/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.62/0.74  fof(f3613,plain,(
% 2.62/0.74    k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK2)),
% 2.62/0.74    inference(subsumption_resolution,[],[f3605,f25])).
% 2.62/0.74  fof(f25,plain,(
% 2.62/0.74    sK1 != sK2),
% 2.62/0.74    inference(cnf_transformation,[],[f17])).
% 2.62/0.74  fof(f17,plain,(
% 2.62/0.74    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.62/0.74    inference(flattening,[],[f16])).
% 2.62/0.74  fof(f16,plain,(
% 2.62/0.74    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.62/0.74    inference(ennf_transformation,[],[f15])).
% 2.62/0.74  fof(f15,negated_conjecture,(
% 2.62/0.74    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.62/0.74    inference(negated_conjecture,[],[f14])).
% 2.62/0.74  fof(f14,conjecture,(
% 2.62/0.74    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.62/0.74  fof(f3605,plain,(
% 2.62/0.74    k2_xboole_0(sK1,sK0) != k2_xboole_0(sK0,sK2) | sK1 = sK2),
% 2.62/0.74    inference(resolution,[],[f3598,f52])).
% 2.62/0.74  fof(f52,plain,(
% 2.62/0.74    ( ! [X0] : (~r1_xboole_0(X0,sK0) | k2_xboole_0(X0,sK0) != k2_xboole_0(sK0,sK2) | sK2 = X0) )),
% 2.62/0.74    inference(forward_demodulation,[],[f46,f29])).
% 2.62/0.74  fof(f46,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(X0,sK0) != k2_xboole_0(sK2,sK0) | ~r1_xboole_0(X0,sK0) | sK2 = X0) )),
% 2.62/0.74    inference(resolution,[],[f23,f41])).
% 2.62/0.74  fof(f41,plain,(
% 2.62/0.74    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X2,X1) | X0 = X2) )),
% 2.62/0.74    inference(cnf_transformation,[],[f21])).
% 2.62/0.74  fof(f21,plain,(
% 2.62/0.74    ! [X0,X1,X2] : (X0 = X2 | ~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1))),
% 2.62/0.74    inference(flattening,[],[f20])).
% 2.62/0.74  fof(f20,plain,(
% 2.62/0.74    ! [X0,X1,X2] : (X0 = X2 | (~r1_xboole_0(X2,X1) | ~r1_xboole_0(X0,X1) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X1)))),
% 2.62/0.74    inference(ennf_transformation,[],[f13])).
% 2.62/0.74  fof(f13,axiom,(
% 2.62/0.74    ! [X0,X1,X2] : ((r1_xboole_0(X2,X1) & r1_xboole_0(X0,X1) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X1)) => X0 = X2)),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).
% 2.62/0.74  fof(f23,plain,(
% 2.62/0.74    r1_xboole_0(sK2,sK0)),
% 2.62/0.74    inference(cnf_transformation,[],[f17])).
% 2.62/0.74  fof(f3598,plain,(
% 2.62/0.74    r1_xboole_0(sK1,sK0)),
% 2.62/0.74    inference(resolution,[],[f3559,f59])).
% 2.62/0.74  fof(f59,plain,(
% 2.62/0.74    r1_xboole_0(sK1,sK3)),
% 2.62/0.74    inference(resolution,[],[f24,f33])).
% 2.62/0.74  fof(f33,plain,(
% 2.62/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.62/0.74    inference(cnf_transformation,[],[f18])).
% 2.62/0.74  fof(f18,plain,(
% 2.62/0.74    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.62/0.74    inference(ennf_transformation,[],[f3])).
% 2.62/0.74  fof(f3,axiom,(
% 2.62/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.62/0.74  fof(f24,plain,(
% 2.62/0.74    r1_xboole_0(sK3,sK1)),
% 2.62/0.74    inference(cnf_transformation,[],[f17])).
% 2.62/0.74  fof(f3559,plain,(
% 2.62/0.74    ( ! [X3] : (~r1_xboole_0(X3,sK3) | r1_xboole_0(X3,sK0)) )),
% 2.62/0.74    inference(superposition,[],[f38,f3526])).
% 2.62/0.74  fof(f3526,plain,(
% 2.62/0.74    sK3 = k2_xboole_0(sK0,sK3)),
% 2.62/0.74    inference(forward_demodulation,[],[f3525,f28])).
% 2.62/0.74  fof(f28,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.62/0.74    inference(cnf_transformation,[],[f4])).
% 2.62/0.74  fof(f4,axiom,(
% 2.62/0.74    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.62/0.74  fof(f3525,plain,(
% 2.62/0.74    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 2.62/0.74    inference(forward_demodulation,[],[f3520,f29])).
% 2.62/0.74  fof(f3520,plain,(
% 2.62/0.74    k2_xboole_0(sK3,k1_xboole_0) = k2_xboole_0(sK3,sK0)),
% 2.62/0.74    inference(superposition,[],[f31,f3499])).
% 2.62/0.74  fof(f3499,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(sK0,sK3)),
% 2.62/0.74    inference(forward_demodulation,[],[f3480,f1969])).
% 2.62/0.74  fof(f1969,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f1809,f1773])).
% 2.62/0.74  fof(f1773,plain,(
% 2.62/0.74    sK0 = k4_xboole_0(sK0,sK2)),
% 2.62/0.74    inference(superposition,[],[f1719,f100])).
% 2.62/0.74  fof(f100,plain,(
% 2.62/0.74    sK0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK2))),
% 2.62/0.74    inference(superposition,[],[f43,f66])).
% 2.62/0.74  fof(f66,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 2.62/0.74    inference(resolution,[],[f51,f44])).
% 2.62/0.74  fof(f44,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.62/0.74    inference(definition_unfolding,[],[f35,f30])).
% 2.62/0.74  fof(f30,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.62/0.74    inference(cnf_transformation,[],[f9])).
% 2.62/0.74  fof(f9,axiom,(
% 2.62/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.62/0.74  fof(f35,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.62/0.74    inference(cnf_transformation,[],[f2])).
% 2.62/0.74  fof(f2,axiom,(
% 2.62/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.62/0.74  fof(f51,plain,(
% 2.62/0.74    r1_xboole_0(sK0,sK2)),
% 2.62/0.74    inference(resolution,[],[f23,f33])).
% 2.62/0.74  fof(f43,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.62/0.74    inference(definition_unfolding,[],[f32,f30])).
% 2.62/0.74  fof(f32,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.62/0.74    inference(cnf_transformation,[],[f11])).
% 2.62/0.74  fof(f11,axiom,(
% 2.62/0.74    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.62/0.74  fof(f1719,plain,(
% 2.62/0.74    ( ! [X2] : (k2_xboole_0(k1_xboole_0,X2) = X2) )),
% 2.62/0.74    inference(forward_demodulation,[],[f1703,f28])).
% 2.62/0.74  fof(f1703,plain,(
% 2.62/0.74    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,k1_xboole_0))) )),
% 2.62/0.74    inference(superposition,[],[f912,f29])).
% 2.62/0.74  fof(f912,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f355,f908])).
% 2.62/0.74  fof(f908,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f898,f50])).
% 2.62/0.74  fof(f50,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 2.62/0.74    inference(resolution,[],[f23,f44])).
% 2.62/0.74  fof(f898,plain,(
% 2.62/0.74    k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) = k4_xboole_0(k1_xboole_0,sK2)),
% 2.62/0.74    inference(superposition,[],[f83,f89])).
% 2.62/0.74  fof(f89,plain,(
% 2.62/0.74    k4_xboole_0(sK2,sK0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f87,f28])).
% 2.62/0.74  fof(f87,plain,(
% 2.62/0.74    k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0)),
% 2.62/0.74    inference(superposition,[],[f31,f50])).
% 2.62/0.74  fof(f83,plain,(
% 2.62/0.74    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.62/0.74    inference(superposition,[],[f36,f50])).
% 2.62/0.74  fof(f36,plain,(
% 2.62/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.62/0.74    inference(cnf_transformation,[],[f8])).
% 2.62/0.74  fof(f8,axiom,(
% 2.62/0.74    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.62/0.74  fof(f355,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k4_xboole_0(k1_xboole_0,sK2),X0))) )),
% 2.62/0.74    inference(superposition,[],[f37,f324])).
% 2.62/0.74  fof(f324,plain,(
% 2.62/0.74    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))),
% 2.62/0.74    inference(superposition,[],[f43,f236])).
% 2.62/0.74  fof(f236,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))),
% 2.62/0.74    inference(resolution,[],[f211,f44])).
% 2.62/0.74  fof(f211,plain,(
% 2.62/0.74    r1_xboole_0(k1_xboole_0,sK2)),
% 2.62/0.74    inference(resolution,[],[f204,f33])).
% 2.62/0.74  fof(f204,plain,(
% 2.62/0.74    r1_xboole_0(sK2,k1_xboole_0)),
% 2.62/0.74    inference(resolution,[],[f194,f23])).
% 2.62/0.74  fof(f194,plain,(
% 2.62/0.74    ( ! [X1] : (~r1_xboole_0(X1,sK0) | r1_xboole_0(X1,k1_xboole_0)) )),
% 2.62/0.74    inference(superposition,[],[f38,f100])).
% 2.62/0.74  fof(f37,plain,(
% 2.62/0.74    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.62/0.74    inference(cnf_transformation,[],[f10])).
% 2.62/0.74  fof(f10,axiom,(
% 2.62/0.74    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.62/0.74  fof(f1809,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f101,f1770])).
% 2.62/0.74  fof(f1770,plain,(
% 2.62/0.74    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 2.62/0.74    inference(superposition,[],[f1719,f993])).
% 2.62/0.74  fof(f993,plain,(
% 2.62/0.74    ( ! [X2] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2))) )),
% 2.62/0.74    inference(superposition,[],[f43,f954])).
% 2.62/0.74  fof(f954,plain,(
% 2.62/0.74    ( ! [X8] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X8))) )),
% 2.62/0.74    inference(resolution,[],[f916,f44])).
% 2.62/0.74  fof(f916,plain,(
% 2.62/0.74    ( ! [X9] : (r1_xboole_0(k1_xboole_0,X9)) )),
% 2.62/0.74    inference(backward_demodulation,[],[f854,f908])).
% 2.62/0.74  fof(f854,plain,(
% 2.62/0.74    ( ! [X9] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,sK2),X9)) )),
% 2.62/0.74    inference(resolution,[],[f848,f33])).
% 2.62/0.74  fof(f848,plain,(
% 2.62/0.74    ( ! [X4] : (r1_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK2))) )),
% 2.62/0.74    inference(subsumption_resolution,[],[f835,f42])).
% 2.62/0.74  fof(f42,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.62/0.74    inference(definition_unfolding,[],[f26,f30])).
% 2.62/0.74  fof(f26,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.62/0.74    inference(cnf_transformation,[],[f5])).
% 2.62/0.74  fof(f5,axiom,(
% 2.62/0.74    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.62/0.74  fof(f835,plain,(
% 2.62/0.74    ( ! [X4] : (r1_xboole_0(X4,k4_xboole_0(k1_xboole_0,sK2)) | k1_xboole_0 != k4_xboole_0(X4,k4_xboole_0(X4,k1_xboole_0))) )),
% 2.62/0.74    inference(resolution,[],[f357,f45])).
% 2.62/0.74  fof(f45,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.62/0.74    inference(definition_unfolding,[],[f34,f30])).
% 2.62/0.74  fof(f34,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.62/0.74    inference(cnf_transformation,[],[f2])).
% 2.62/0.74  fof(f357,plain,(
% 2.62/0.74    ( ! [X2] : (~r1_xboole_0(X2,k1_xboole_0) | r1_xboole_0(X2,k4_xboole_0(k1_xboole_0,sK2))) )),
% 2.62/0.74    inference(superposition,[],[f39,f324])).
% 2.62/0.74  fof(f39,plain,(
% 2.62/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.62/0.74    inference(cnf_transformation,[],[f19])).
% 2.62/0.74  fof(f19,plain,(
% 2.62/0.74    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.62/0.74    inference(ennf_transformation,[],[f12])).
% 2.62/0.74  fof(f12,axiom,(
% 2.62/0.74    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.62/0.74  fof(f101,plain,(
% 2.62/0.74    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK2),X0))) )),
% 2.62/0.74    inference(superposition,[],[f36,f66])).
% 2.62/0.74  fof(f3480,plain,(
% 2.62/0.74    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 2.62/0.74    inference(superposition,[],[f2215,f22])).
% 2.62/0.74  fof(f22,plain,(
% 2.62/0.74    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.62/0.74    inference(cnf_transformation,[],[f17])).
% 2.62/0.74  fof(f2215,plain,(
% 2.62/0.74    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK2,X0))) )),
% 2.62/0.74    inference(superposition,[],[f36,f1773])).
% 2.62/0.74  fof(f31,plain,(
% 2.62/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.62/0.74    inference(cnf_transformation,[],[f6])).
% 2.62/0.74  fof(f6,axiom,(
% 2.62/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.62/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.62/0.74  fof(f38,plain,(
% 2.62/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.62/0.74    inference(cnf_transformation,[],[f19])).
% 2.62/0.74  fof(f3844,plain,(
% 2.62/0.74    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,sK2)),
% 2.62/0.74    inference(backward_demodulation,[],[f2369,f3841])).
% 2.62/0.74  fof(f3841,plain,(
% 2.62/0.74    sK2 = k2_xboole_0(sK1,sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f3840,f28])).
% 2.62/0.74  fof(f3840,plain,(
% 2.62/0.74    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f3837,f29])).
% 2.62/0.74  fof(f3837,plain,(
% 2.62/0.74    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)),
% 2.62/0.74    inference(superposition,[],[f31,f3820])).
% 2.62/0.74  fof(f3820,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f3802,f2310])).
% 2.62/0.74  fof(f2310,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) )),
% 2.62/0.74    inference(superposition,[],[f2030,f29])).
% 2.62/0.74  fof(f2030,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f1810,f1775])).
% 2.62/0.74  fof(f1775,plain,(
% 2.62/0.74    sK1 = k4_xboole_0(sK1,sK3)),
% 2.62/0.74    inference(superposition,[],[f1719,f114])).
% 2.62/0.74  fof(f114,plain,(
% 2.62/0.74    sK1 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK1,sK3))),
% 2.62/0.74    inference(superposition,[],[f43,f72])).
% 2.62/0.74  fof(f72,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.62/0.74    inference(resolution,[],[f59,f44])).
% 2.62/0.74  fof(f1810,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f115,f1770])).
% 2.62/0.74  fof(f115,plain,(
% 2.62/0.74    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK3),X0))) )),
% 2.62/0.74    inference(superposition,[],[f36,f72])).
% 2.62/0.74  fof(f3802,plain,(
% 2.62/0.74    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 2.62/0.74    inference(superposition,[],[f2222,f2863])).
% 2.62/0.74  fof(f2863,plain,(
% 2.62/0.74    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 2.62/0.74    inference(forward_demodulation,[],[f2848,f2369])).
% 2.62/0.74  fof(f2848,plain,(
% 2.62/0.74    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.62/0.74    inference(superposition,[],[f2443,f80])).
% 2.62/0.74  fof(f80,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 2.62/0.74    inference(forward_demodulation,[],[f74,f37])).
% 2.62/0.74  fof(f74,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 2.62/0.74    inference(superposition,[],[f37,f22])).
% 2.62/0.74  fof(f2443,plain,(
% 2.62/0.74    ( ! [X3] : (k2_xboole_0(X3,sK2) = k2_xboole_0(sK2,k2_xboole_0(X3,sK2))) )),
% 2.62/0.74    inference(superposition,[],[f2063,f29])).
% 2.62/0.74  fof(f2063,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(sK2,X0) = k2_xboole_0(sK2,k2_xboole_0(sK2,X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f457,f1777])).
% 2.62/0.74  fof(f1777,plain,(
% 2.62/0.74    sK2 = k4_xboole_0(sK2,sK0)),
% 2.62/0.74    inference(superposition,[],[f1719,f82])).
% 2.62/0.74  fof(f82,plain,(
% 2.62/0.74    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 2.62/0.74    inference(superposition,[],[f43,f50])).
% 2.62/0.74  fof(f457,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK2,sK0),X0) = k2_xboole_0(k4_xboole_0(sK2,sK0),k2_xboole_0(sK2,X0))) )),
% 2.62/0.74    inference(superposition,[],[f37,f89])).
% 2.62/0.74  fof(f2222,plain,(
% 2.62/0.74    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK3,X0))) )),
% 2.62/0.74    inference(superposition,[],[f36,f1775])).
% 2.62/0.74  fof(f2369,plain,(
% 2.62/0.74    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.62/0.74    inference(forward_demodulation,[],[f2368,f28])).
% 2.62/0.74  fof(f2368,plain,(
% 2.62/0.74    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 2.62/0.74    inference(forward_demodulation,[],[f2367,f1264])).
% 2.62/0.74  fof(f1264,plain,(
% 2.62/0.74    k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.62/0.74    inference(superposition,[],[f278,f22])).
% 2.62/0.74  fof(f278,plain,(
% 2.62/0.74    ( ! [X0] : (k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK2,k2_xboole_0(X0,sK3))) )),
% 2.62/0.74    inference(superposition,[],[f80,f29])).
% 2.62/0.74  fof(f2367,plain,(
% 2.62/0.74    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.62/0.74    inference(forward_demodulation,[],[f2359,f29])).
% 2.62/0.74  fof(f2359,plain,(
% 2.62/0.74    k2_xboole_0(k2_xboole_0(sK0,sK1),k1_xboole_0) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 2.62/0.74    inference(superposition,[],[f31,f2259])).
% 2.62/0.74  fof(f2259,plain,(
% 2.62/0.74    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.62/0.74    inference(superposition,[],[f2080,f22])).
% 2.62/0.74  fof(f2080,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK2,X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f1807,f1777])).
% 2.62/0.74  fof(f1807,plain,(
% 2.62/0.74    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(k4_xboole_0(sK2,sK0),X0))) )),
% 2.62/0.74    inference(backward_demodulation,[],[f83,f1770])).
% 2.62/0.74  % SZS output end Proof for theBenchmark
% 2.62/0.74  % (9529)------------------------------
% 2.62/0.74  % (9529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.62/0.74  % (9529)Termination reason: Refutation
% 2.62/0.74  
% 2.62/0.74  % (9529)Memory used [KB]: 3070
% 2.62/0.74  % (9529)Time elapsed: 0.324 s
% 2.62/0.74  % (9529)------------------------------
% 2.62/0.74  % (9529)------------------------------
% 2.62/0.75  % (9506)Success in time 0.38 s
%------------------------------------------------------------------------------
