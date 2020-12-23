%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  146 (3827 expanded)
%              Number of leaves         :   15 (1130 expanded)
%              Depth                    :   58
%              Number of atoms          :  192 (9489 expanded)
%              Number of equality atoms :  129 (3736 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f761,plain,(
    $false ),
    inference(subsumption_resolution,[],[f751,f31])).

fof(f31,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f751,plain,(
    sK1 = sK2 ),
    inference(superposition,[],[f738,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f738,plain,(
    sK1 = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f737,f409])).

fof(f409,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f407,f34])).

fof(f407,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f39,f395])).

fof(f395,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f349,f84])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f44,f71])).

fof(f71,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f70,f33])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f70,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f38,f54])).

fof(f54,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f47,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f47,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f29,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f349,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f244,f348])).

fof(f348,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f339,f89])).

fof(f89,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f88,f59])).

fof(f59,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f49,f35])).

fof(f49,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f30,f42])).

fof(f30,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f37,f75])).

fof(f75,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f74,f33])).

fof(f74,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f38,f59])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f339,plain,(
    k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f101,f104])).

fof(f104,plain,(
    sK3 = k2_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f102,f34])).

fof(f102,plain,(
    k2_xboole_0(sK3,sK3) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f39,f89])).

fof(f101,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f44,f89])).

fof(f244,plain,(
    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f96,f28])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f96,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f44,f86])).

fof(f86,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f85,f54])).

fof(f85,plain,(
    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f37,f71])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f737,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f735,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f735,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f39,f658])).

fof(f658,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f657,f95])).

fof(f95,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f94,f65])).

fof(f65,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f30,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f94,plain,(
    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f37,f83])).

fof(f83,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f82,f33])).

fof(f82,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f38,f65])).

fof(f657,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f477,f579])).

fof(f579,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f93,f569])).

fof(f569,plain,(
    sK0 = sK3 ),
    inference(forward_demodulation,[],[f564,f33])).

fof(f564,plain,(
    sK3 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f555,f563])).

fof(f563,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f561,f33])).

fof(f561,plain,(
    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f38,f550])).

fof(f550,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f549,f513])).

fof(f513,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(forward_demodulation,[],[f512,f89])).

fof(f512,plain,(
    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK0) ),
    inference(forward_demodulation,[],[f511,f197])).

fof(f197,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f87,f36])).

fof(f87,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f44,f75])).

fof(f511,plain,(
    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f38,f506])).

fof(f506,plain,(
    sK3 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f503,f33])).

fof(f503,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f484])).

fof(f484,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f476,f252])).

fof(f252,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f243,f86])).

fof(f243,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f96,f99])).

fof(f99,plain,(
    sK2 = k2_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f97,f34])).

fof(f97,plain,(
    k2_xboole_0(sK2,sK2) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f39,f86])).

fof(f476,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(superposition,[],[f101,f472])).

fof(f472,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f470,f157])).

fof(f157,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f156,f28])).

fof(f156,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f155,f36])).

fof(f155,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f152,f39])).

fof(f152,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f39,f141])).

fof(f141,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f40,f28])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f470,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f39,f449])).

fof(f449,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f141,f447])).

fof(f447,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f446,f33])).

fof(f446,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f38,f437])).

fof(f437,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f434,f35])).

fof(f434,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f430,f42])).

fof(f430,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f428,f43])).

fof(f428,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f425,f56])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f47,f54])).

fof(f425,plain,
    ( r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | r1_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f41,f422])).

fof(f422,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f421,f89])).

fof(f421,plain,(
    k4_xboole_0(sK3,sK3) = k3_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f37,f419])).

fof(f419,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f417,f75])).

fof(f417,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f87,f409])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f549,plain,(
    k4_xboole_0(sK3,sK0) = k3_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f543,f37])).

fof(f543,plain,(
    k4_xboole_0(sK3,sK0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f101,f520])).

fof(f520,plain,(
    sK0 = k2_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f229,f519])).

fof(f519,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f517,f34])).

fof(f517,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f39,f513])).

fof(f229,plain,(
    k2_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1)) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f226,f36])).

fof(f226,plain,(
    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f39,f218])).

fof(f218,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f210,f106])).

fof(f106,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f44,f92])).

fof(f92,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f91,f62])).

fof(f62,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f46,f42])).

fof(f46,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f29,f43])).

fof(f91,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f37,f79])).

fof(f79,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f78,f33])).

fof(f78,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f38,f62])).

fof(f210,plain,(
    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f90,f28])).

fof(f90,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f44,f79])).

fof(f555,plain,(
    sK3 = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f227,f553])).

fof(f553,plain,(
    sK3 = k3_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f552,f33])).

fof(f552,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f551,f227])).

fof(f551,plain,(
    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f546,f205])).

fof(f205,plain,(
    ! [X2] : k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,X2) ),
    inference(forward_demodulation,[],[f199,f87])).

fof(f199,plain,(
    ! [X2] : k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f87,f39])).

fof(f546,plain,(
    k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f40,f520])).

fof(f227,plain,(
    k3_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(superposition,[],[f37,f218])).

fof(f93,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f44,f83])).

fof(f477,plain,(
    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f93,f472])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:21:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (5260)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (5252)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (5259)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (5257)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5268)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (5268)Refutation not found, incomplete strategy% (5268)------------------------------
% 0.21/0.53  % (5268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5268)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5268)Memory used [KB]: 10618
% 0.21/0.53  % (5268)Time elapsed: 0.118 s
% 0.21/0.53  % (5268)------------------------------
% 0.21/0.53  % (5268)------------------------------
% 0.21/0.53  % (5275)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (5254)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (5255)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (5277)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5281)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5256)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (5258)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (5274)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (5278)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (5272)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (5279)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (5251)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (5265)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (5273)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (5262)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (5280)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (5267)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (5266)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (5264)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (5266)Refutation not found, incomplete strategy% (5266)------------------------------
% 0.21/0.55  % (5266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5266)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5266)Memory used [KB]: 6140
% 0.21/0.55  % (5266)Time elapsed: 0.001 s
% 0.21/0.55  % (5266)------------------------------
% 0.21/0.55  % (5266)------------------------------
% 0.21/0.55  % (5270)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (5263)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (5275)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f761,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f751,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    sK1 != sK2),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 0.21/0.56    inference(ennf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.21/0.56    inference(negated_conjecture,[],[f14])).
% 0.21/0.56  fof(f14,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.21/0.56  fof(f751,plain,(
% 0.21/0.56    sK1 = sK2),
% 0.21/0.56    inference(superposition,[],[f738,f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.56  fof(f738,plain,(
% 0.21/0.56    sK1 = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f737,f409])).
% 0.21/0.56  fof(f409,plain,(
% 0.21/0.56    sK1 = k2_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f407,f34])).
% 0.21/0.56  fof(f407,plain,(
% 0.21/0.56    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(superposition,[],[f39,f395])).
% 0.21/0.56  fof(f395,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.21/0.56    inference(superposition,[],[f349,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 0.21/0.56    inference(superposition,[],[f44,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    sK2 = k4_xboole_0(sK2,sK0)),
% 0.21/0.56    inference(forward_demodulation,[],[f70,f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f38,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 0.21/0.56    inference(resolution,[],[f47,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK0))) )),
% 0.21/0.56    inference(resolution,[],[f29,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(rectify,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    r1_xboole_0(sK2,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.56  fof(f349,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(backward_demodulation,[],[f244,f348])).
% 0.21/0.56  fof(f348,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f339,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f88,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 0.21/0.56    inference(resolution,[],[f49,f35])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK3,sK1))) )),
% 0.21/0.56    inference(resolution,[],[f30,f42])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    r1_xboole_0(sK3,sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK3)),
% 0.21/0.56    inference(superposition,[],[f37,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    sK3 = k4_xboole_0(sK3,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f74,f33])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f38,f59])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.56  fof(f339,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,sK3)),
% 0.21/0.56    inference(superposition,[],[f101,f104])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    sK3 = k2_xboole_0(sK3,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f102,f34])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    k2_xboole_0(sK3,sK3) = k2_xboole_0(sK3,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f39,f89])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK3,k2_xboole_0(sK3,X0))) )),
% 0.21/0.56    inference(superposition,[],[f44,f89])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f96,f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(superposition,[],[f44,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f85,f54])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2)),
% 0.21/0.56    inference(superposition,[],[f37,f71])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.56  fof(f737,plain,(
% 0.21/0.56    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f735,f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.56  fof(f735,plain,(
% 0.21/0.56    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)),
% 0.21/0.56    inference(superposition,[],[f39,f658])).
% 0.21/0.56  fof(f658,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f657,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f94,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 0.21/0.56    inference(resolution,[],[f53,f35])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK3))) )),
% 0.21/0.56    inference(resolution,[],[f48,f42])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    r1_xboole_0(sK1,sK3)),
% 0.21/0.56    inference(resolution,[],[f30,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1)),
% 0.21/0.56    inference(superposition,[],[f37,f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    sK1 = k4_xboole_0(sK1,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f82,f33])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f38,f65])).
% 0.21/0.56  fof(f657,plain,(
% 0.21/0.56    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(backward_demodulation,[],[f477,f579])).
% 0.21/0.56  fof(f579,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK1,X0) = k4_xboole_0(sK1,k2_xboole_0(sK0,X0))) )),
% 0.21/0.56    inference(backward_demodulation,[],[f93,f569])).
% 0.21/0.56  fof(f569,plain,(
% 0.21/0.56    sK0 = sK3),
% 0.21/0.56    inference(forward_demodulation,[],[f564,f33])).
% 0.21/0.56  fof(f564,plain,(
% 0.21/0.56    sK3 = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.56    inference(backward_demodulation,[],[f555,f563])).
% 0.21/0.56  fof(f563,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f561,f33])).
% 0.21/0.56  fof(f561,plain,(
% 0.21/0.56    k4_xboole_0(k1_xboole_0,sK1) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f38,f550])).
% 0.21/0.56  fof(f550,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f549,f513])).
% 0.21/0.56  fof(f513,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 0.21/0.56    inference(forward_demodulation,[],[f512,f89])).
% 0.21/0.56  fof(f512,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,sK0)),
% 0.21/0.56    inference(forward_demodulation,[],[f511,f197])).
% 0.21/0.56  fof(f197,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 0.21/0.56    inference(superposition,[],[f87,f36])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 0.21/0.56    inference(superposition,[],[f44,f75])).
% 0.21/0.56  fof(f511,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK3) = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f38,f506])).
% 0.21/0.56  fof(f506,plain,(
% 0.21/0.56    sK3 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f503,f33])).
% 0.21/0.56  fof(f503,plain,(
% 0.21/0.56    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f37,f484])).
% 0.21/0.56  fof(f484,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f476,f252])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f243,f86])).
% 0.21/0.56  fof(f243,plain,(
% 0.21/0.56    k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.56    inference(superposition,[],[f96,f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    sK2 = k2_xboole_0(sK2,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f97,f34])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    k2_xboole_0(sK2,sK2) = k2_xboole_0(sK2,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f39,f86])).
% 0.21/0.56  fof(f476,plain,(
% 0.21/0.56    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k1_xboole_0,sK2)),
% 0.21/0.56    inference(superposition,[],[f101,f472])).
% 0.21/0.56  fof(f472,plain,(
% 0.21/0.56    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f470,f157])).
% 0.21/0.56  fof(f157,plain,(
% 0.21/0.56    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f156,f28])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f155,f36])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f152,f39])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 0.21/0.56    inference(superposition,[],[f39,f141])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.21/0.56    inference(superposition,[],[f40,f28])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.56  fof(f470,plain,(
% 0.21/0.56    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f39,f449])).
% 0.21/0.56  fof(f449,plain,(
% 0.21/0.56    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 0.21/0.56    inference(backward_demodulation,[],[f141,f447])).
% 0.21/0.56  fof(f447,plain,(
% 0.21/0.56    sK2 = k4_xboole_0(sK2,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f446,f33])).
% 0.21/0.56  fof(f446,plain,(
% 0.21/0.56    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3)),
% 0.21/0.56    inference(superposition,[],[f38,f437])).
% 0.21/0.56  fof(f437,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 0.21/0.56    inference(resolution,[],[f434,f35])).
% 0.21/0.56  fof(f434,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK3))) )),
% 0.21/0.56    inference(resolution,[],[f430,f42])).
% 0.21/0.56  fof(f430,plain,(
% 0.21/0.56    r1_xboole_0(sK2,sK3)),
% 0.21/0.56    inference(resolution,[],[f428,f43])).
% 0.21/0.56  fof(f428,plain,(
% 0.21/0.56    r1_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f425,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(backward_demodulation,[],[f47,f54])).
% 0.21/0.56  fof(f425,plain,(
% 0.21/0.56    r2_hidden(sK5(sK3,sK2),k1_xboole_0) | r1_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(superposition,[],[f41,f422])).
% 0.21/0.56  fof(f422,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f421,f89])).
% 0.21/0.56  fof(f421,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK3) = k3_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(superposition,[],[f37,f419])).
% 0.21/0.56  fof(f419,plain,(
% 0.21/0.56    sK3 = k4_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f417,f75])).
% 0.21/0.56  fof(f417,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2)),
% 0.21/0.56    inference(superposition,[],[f87,f409])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f549,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK0) = k3_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f543,f37])).
% 0.21/0.56  fof(f543,plain,(
% 0.21/0.56    k4_xboole_0(sK3,sK0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(superposition,[],[f101,f520])).
% 0.21/0.56  fof(f520,plain,(
% 0.21/0.56    sK0 = k2_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(backward_demodulation,[],[f229,f519])).
% 0.21/0.56  fof(f519,plain,(
% 0.21/0.56    sK0 = k2_xboole_0(sK0,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f517,f34])).
% 0.21/0.56  fof(f517,plain,(
% 0.21/0.56    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 0.21/0.56    inference(superposition,[],[f39,f513])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    k2_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1)) = k2_xboole_0(sK0,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f226,f36])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    k2_xboole_0(sK3,sK0) = k2_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(superposition,[],[f39,f218])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    k4_xboole_0(sK0,sK3) = k4_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.56    inference(forward_demodulation,[],[f210,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK0,k2_xboole_0(sK0,X0))) )),
% 0.21/0.56    inference(superposition,[],[f44,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.21/0.56    inference(forward_demodulation,[],[f91,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.21/0.56    inference(resolution,[],[f51,f35])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK2))) )),
% 0.21/0.56    inference(resolution,[],[f46,f42])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    r1_xboole_0(sK0,sK2)),
% 0.21/0.56    inference(resolution,[],[f29,f43])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)),
% 0.21/0.56    inference(superposition,[],[f37,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    sK0 = k4_xboole_0(sK0,sK2)),
% 0.21/0.56    inference(forward_demodulation,[],[f78,f33])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 0.21/0.56    inference(superposition,[],[f38,f62])).
% 0.21/0.56  fof(f210,plain,(
% 0.21/0.56    k4_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k2_xboole_0(sK0,sK1))),
% 0.21/0.56    inference(superposition,[],[f90,f28])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK0,X0)) )),
% 0.21/0.56    inference(superposition,[],[f44,f79])).
% 0.21/0.56  fof(f555,plain,(
% 0.21/0.56    sK3 = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(backward_demodulation,[],[f227,f553])).
% 0.21/0.56  fof(f553,plain,(
% 0.21/0.56    sK3 = k3_xboole_0(sK0,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f552,f33])).
% 0.21/0.56  fof(f552,plain,(
% 0.21/0.56    k4_xboole_0(sK3,k1_xboole_0) = k3_xboole_0(sK0,sK3)),
% 0.21/0.56    inference(forward_demodulation,[],[f551,f227])).
% 0.21/0.56  fof(f551,plain,(
% 0.21/0.56    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(forward_demodulation,[],[f546,f205])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    ( ! [X2] : (k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,X2)) )),
% 0.21/0.56    inference(forward_demodulation,[],[f199,f87])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    ( ! [X2] : (k4_xboole_0(sK3,k4_xboole_0(X2,sK1)) = k4_xboole_0(sK3,k2_xboole_0(sK1,X2))) )),
% 0.21/0.56    inference(superposition,[],[f87,f39])).
% 0.21/0.56  fof(f546,plain,(
% 0.21/0.56    k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1)) = k4_xboole_0(sK3,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(superposition,[],[f40,f520])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    k3_xboole_0(sK0,sK3) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,sK1))),
% 0.21/0.56    inference(superposition,[],[f37,f218])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 0.21/0.56    inference(superposition,[],[f44,f83])).
% 0.21/0.56  fof(f477,plain,(
% 0.21/0.56    k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK2)),
% 0.21/0.56    inference(superposition,[],[f93,f472])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (5275)------------------------------
% 0.21/0.56  % (5275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5275)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (5275)Memory used [KB]: 2046
% 0.21/0.56  % (5275)Time elapsed: 0.114 s
% 0.21/0.56  % (5275)------------------------------
% 0.21/0.56  % (5275)------------------------------
% 0.21/0.56  % (5276)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (5250)Success in time 0.196 s
%------------------------------------------------------------------------------
