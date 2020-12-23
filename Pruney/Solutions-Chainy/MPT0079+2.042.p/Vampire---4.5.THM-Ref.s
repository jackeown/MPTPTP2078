%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:57 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 598 expanded)
%              Number of leaves         :   18 ( 176 expanded)
%              Depth                    :   35
%              Number of atoms          :  167 (1450 expanded)
%              Number of equality atoms :   98 ( 606 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2534,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2516,f35])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).

fof(f25,plain,
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

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f2516,plain,(
    sK1 = sK2 ),
    inference(superposition,[],[f2510,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f2510,plain,(
    sK1 = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2509,f172])).

fof(f172,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f170,f37])).

fof(f170,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f45,f168])).

fof(f168,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f167,f95])).

fof(f95,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f94,f61])).

fof(f61,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f54,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f33,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f94,plain,(
    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f42,f78])).

fof(f78,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f77,f36])).

fof(f36,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f77,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f43,f61])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f167,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f166,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f51,f78])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f166,plain,(
    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f43,f163])).

fof(f163,plain,(
    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f160,f36])).

fof(f160,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f42,f155])).

fof(f155,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f153,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f153,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f40,f32])).

fof(f32,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2509,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2506,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2506,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f45,f2498])).

fof(f2498,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f2486,f503])).

fof(f503,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f384,f41])).

fof(f384,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(backward_demodulation,[],[f126,f380])).

fof(f380,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f161,f373])).

fof(f373,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) ),
    inference(resolution,[],[f337,f50])).

fof(f337,plain,(
    ! [X5] : r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X5))) ),
    inference(superposition,[],[f40,f154])).

fof(f154,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f151,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f151,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f52,f32])).

fof(f161,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f158,f52])).

fof(f158,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) ),
    inference(superposition,[],[f51,f155])).

fof(f126,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f51,f110])).

fof(f110,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f109,f72])).

fof(f72,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f60,f38])).

fof(f60,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f55,f47])).

fof(f55,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f34,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f34,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,(
    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f42,f90])).

fof(f90,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f89,f36])).

fof(f89,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f43,f72])).

fof(f2486,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f107,f372])).

fof(f372,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f370,f185])).

fof(f185,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f184,f32])).

fof(f184,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f183,f41])).

fof(f183,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f180,f45])).

fof(f180,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f45,f152])).

fof(f152,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f44,f32])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f370,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f45,f359])).

fof(f359,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f152,f356])).

fof(f356,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f355,f36])).

fof(f355,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f43,f350])).

fof(f350,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f349,f38])).

fof(f349,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK2,sK3)) ),
    inference(resolution,[],[f345,f47])).

fof(f345,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f327,f48])).

fof(f327,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(subsumption_resolution,[],[f324,f63])).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f54,f61])).

fof(f324,plain,
    ( r2_hidden(sK5(sK3,sK2),k1_xboole_0)
    | r1_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f46,f323])).

fof(f323,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f322,f100])).

fof(f100,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f99,f66])).

fof(f66,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f34,f47])).

fof(f99,plain,(
    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f42,f82])).

fof(f82,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f81,f36])).

fof(f81,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f43,f66])).

fof(f322,plain,(
    k4_xboole_0(sK3,sK3) = k3_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f42,f312])).

fof(f312,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f302,f82])).

fof(f302,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f97,f172])).

fof(f97,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f51,f82])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[],[f51,f90])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:07:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (16968)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (16989)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (16981)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (16981)Refutation not found, incomplete strategy% (16981)------------------------------
% 0.20/0.54  % (16981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16981)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16981)Memory used [KB]: 6140
% 0.20/0.55  % (16981)Time elapsed: 0.004 s
% 0.20/0.55  % (16981)------------------------------
% 0.20/0.55  % (16981)------------------------------
% 0.20/0.55  % (16980)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (16988)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (16973)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (16970)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.57  % (16978)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.58  % (16971)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.58  % (16967)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.62/0.59  % (16969)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.62/0.59  % (16966)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.59  % (16992)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.62/0.59  % (16972)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.62/0.59  % (16990)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.62/0.59  % (16982)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.62/0.59  % (16984)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.62/0.60  % (16983)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.62/0.60  % (16993)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.60  % (16983)Refutation not found, incomplete strategy% (16983)------------------------------
% 1.62/0.60  % (16983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (16983)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (16983)Memory used [KB]: 10618
% 1.62/0.60  % (16983)Time elapsed: 0.174 s
% 1.62/0.60  % (16983)------------------------------
% 1.62/0.60  % (16983)------------------------------
% 1.62/0.60  % (16975)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.84/0.60  % (16977)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.84/0.60  % (16974)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.84/0.61  % (16991)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.84/0.61  % (16994)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.84/0.61  % (16985)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.84/0.61  % (16986)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.84/0.61  % (16995)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.84/0.61  % (16976)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.84/0.63  % (16987)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.84/0.64  % (16979)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.21/0.68  % (16989)Refutation found. Thanks to Tanya!
% 2.21/0.68  % SZS status Theorem for theBenchmark
% 2.21/0.68  % SZS output start Proof for theBenchmark
% 2.21/0.68  fof(f2534,plain,(
% 2.21/0.68    $false),
% 2.21/0.68    inference(subsumption_resolution,[],[f2516,f35])).
% 2.21/0.68  fof(f35,plain,(
% 2.21/0.68    sK1 != sK2),
% 2.21/0.68    inference(cnf_transformation,[],[f26])).
% 2.21/0.68  fof(f26,plain,(
% 2.21/0.68    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f25])).
% 2.21/0.68  fof(f25,plain,(
% 2.21/0.68    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f21,plain,(
% 2.21/0.68    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 2.21/0.68    inference(flattening,[],[f20])).
% 2.21/0.68  fof(f20,plain,(
% 2.21/0.68    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 2.21/0.68    inference(ennf_transformation,[],[f17])).
% 2.21/0.68  fof(f17,negated_conjecture,(
% 2.21/0.68    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.21/0.68    inference(negated_conjecture,[],[f16])).
% 2.21/0.68  fof(f16,conjecture,(
% 2.21/0.68    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 2.21/0.68  fof(f2516,plain,(
% 2.21/0.68    sK1 = sK2),
% 2.21/0.68    inference(superposition,[],[f2510,f37])).
% 2.21/0.68  fof(f37,plain,(
% 2.21/0.68    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.68    inference(cnf_transformation,[],[f7])).
% 2.21/0.68  fof(f7,axiom,(
% 2.21/0.68    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.21/0.68  fof(f2510,plain,(
% 2.21/0.68    sK1 = k2_xboole_0(sK2,k1_xboole_0)),
% 2.21/0.68    inference(forward_demodulation,[],[f2509,f172])).
% 2.21/0.68  fof(f172,plain,(
% 2.21/0.68    sK1 = k2_xboole_0(sK1,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f170,f37])).
% 2.21/0.68  fof(f170,plain,(
% 2.21/0.68    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 2.21/0.68    inference(superposition,[],[f45,f168])).
% 2.21/0.68  fof(f168,plain,(
% 2.21/0.68    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 2.21/0.68    inference(forward_demodulation,[],[f167,f95])).
% 2.21/0.68  fof(f95,plain,(
% 2.21/0.68    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f94,f61])).
% 2.21/0.68  fof(f61,plain,(
% 2.21/0.68    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 2.21/0.68    inference(resolution,[],[f54,f38])).
% 2.21/0.68  fof(f38,plain,(
% 2.21/0.68    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 2.21/0.68    inference(cnf_transformation,[],[f28])).
% 2.21/0.68  fof(f28,plain,(
% 2.21/0.68    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f27])).
% 2.21/0.68  fof(f27,plain,(
% 2.21/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f22,plain,(
% 2.21/0.68    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.21/0.68    inference(ennf_transformation,[],[f5])).
% 2.21/0.68  fof(f5,axiom,(
% 2.21/0.68    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.21/0.68  fof(f54,plain,(
% 2.21/0.68    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK0))) )),
% 2.21/0.68    inference(resolution,[],[f33,f47])).
% 2.21/0.68  fof(f47,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f30])).
% 2.21/0.68  fof(f30,plain,(
% 2.21/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.21/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f29])).
% 2.21/0.68  fof(f29,plain,(
% 2.21/0.68    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 2.21/0.68    introduced(choice_axiom,[])).
% 2.21/0.68  fof(f23,plain,(
% 2.21/0.68    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.21/0.68    inference(ennf_transformation,[],[f19])).
% 2.21/0.68  fof(f19,plain,(
% 2.21/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.21/0.68    inference(rectify,[],[f4])).
% 2.21/0.68  fof(f4,axiom,(
% 2.21/0.68    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.21/0.68  fof(f33,plain,(
% 2.21/0.68    r1_xboole_0(sK2,sK0)),
% 2.21/0.68    inference(cnf_transformation,[],[f26])).
% 2.21/0.68  fof(f94,plain,(
% 2.21/0.68    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2)),
% 2.21/0.68    inference(superposition,[],[f42,f78])).
% 2.21/0.68  fof(f78,plain,(
% 2.21/0.68    sK2 = k4_xboole_0(sK2,sK0)),
% 2.21/0.68    inference(forward_demodulation,[],[f77,f36])).
% 2.21/0.68  fof(f36,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.68    inference(cnf_transformation,[],[f9])).
% 2.21/0.68  fof(f9,axiom,(
% 2.21/0.68    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.21/0.68  fof(f77,plain,(
% 2.21/0.68    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 2.21/0.68    inference(superposition,[],[f43,f61])).
% 2.21/0.68  fof(f43,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f12])).
% 2.21/0.68  fof(f12,axiom,(
% 2.21/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.21/0.68  fof(f42,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f13])).
% 2.21/0.68  fof(f13,axiom,(
% 2.21/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.68  fof(f167,plain,(
% 2.21/0.68    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,sK1)),
% 2.21/0.68    inference(forward_demodulation,[],[f166,f92])).
% 2.21/0.68  fof(f92,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 2.21/0.68    inference(superposition,[],[f51,f78])).
% 2.21/0.68  fof(f51,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f11])).
% 2.21/0.68  fof(f11,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.21/0.68  fof(f166,plain,(
% 2.21/0.68    k4_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(superposition,[],[f43,f163])).
% 2.21/0.68  fof(f163,plain,(
% 2.21/0.68    sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(forward_demodulation,[],[f160,f36])).
% 2.21/0.68  fof(f160,plain,(
% 2.21/0.68    k4_xboole_0(sK2,k1_xboole_0) = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(superposition,[],[f42,f155])).
% 2.21/0.68  fof(f155,plain,(
% 2.21/0.68    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(resolution,[],[f153,f50])).
% 2.21/0.68  fof(f50,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f31])).
% 2.21/0.68  fof(f31,plain,(
% 2.21/0.68    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.21/0.68    inference(nnf_transformation,[],[f6])).
% 2.21/0.68  fof(f6,axiom,(
% 2.21/0.68    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.21/0.68  fof(f153,plain,(
% 2.21/0.68    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(superposition,[],[f40,f32])).
% 2.21/0.68  fof(f32,plain,(
% 2.21/0.68    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 2.21/0.68    inference(cnf_transformation,[],[f26])).
% 2.21/0.68  fof(f40,plain,(
% 2.21/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f15])).
% 2.21/0.68  fof(f15,axiom,(
% 2.21/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.21/0.68  fof(f45,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f8])).
% 2.21/0.68  fof(f8,axiom,(
% 2.21/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.21/0.68  fof(f2509,plain,(
% 2.21/0.68    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f2506,f41])).
% 2.21/0.68  fof(f41,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f1])).
% 2.21/0.68  fof(f1,axiom,(
% 2.21/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.21/0.68  fof(f2506,plain,(
% 2.21/0.68    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)),
% 2.21/0.68    inference(superposition,[],[f45,f2498])).
% 2.21/0.68  fof(f2498,plain,(
% 2.21/0.68    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f2486,f503])).
% 2.21/0.68  fof(f503,plain,(
% 2.21/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(X0,sK1))) )),
% 2.21/0.68    inference(superposition,[],[f384,f41])).
% 2.21/0.68  fof(f384,plain,(
% 2.21/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 2.21/0.68    inference(backward_demodulation,[],[f126,f380])).
% 2.21/0.68  fof(f380,plain,(
% 2.21/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.21/0.68    inference(backward_demodulation,[],[f161,f373])).
% 2.21/0.68  fof(f373,plain,(
% 2.21/0.68    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0)))) )),
% 2.21/0.68    inference(resolution,[],[f337,f50])).
% 2.21/0.68  fof(f337,plain,(
% 2.21/0.68    ( ! [X5] : (r1_tarski(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X5)))) )),
% 2.21/0.68    inference(superposition,[],[f40,f154])).
% 2.21/0.68  fof(f154,plain,(
% 2.21/0.68    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 2.21/0.68    inference(forward_demodulation,[],[f151,f52])).
% 2.21/0.68  fof(f52,plain,(
% 2.21/0.68    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.21/0.68    inference(cnf_transformation,[],[f14])).
% 2.21/0.68  fof(f14,axiom,(
% 2.21/0.68    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 2.21/0.68  fof(f151,plain,(
% 2.21/0.68    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 2.21/0.68    inference(superposition,[],[f52,f32])).
% 2.21/0.68  fof(f161,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,X0)))) )),
% 2.21/0.68    inference(forward_demodulation,[],[f158,f52])).
% 2.21/0.68  fof(f158,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(sK0,sK1),X0))) )),
% 2.21/0.68    inference(superposition,[],[f51,f155])).
% 2.21/0.68  fof(f126,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(sK1,k2_xboole_0(sK1,X0))) )),
% 2.21/0.68    inference(superposition,[],[f51,f110])).
% 2.21/0.68  fof(f110,plain,(
% 2.21/0.68    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 2.21/0.68    inference(forward_demodulation,[],[f109,f72])).
% 2.21/0.68  fof(f72,plain,(
% 2.21/0.68    k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 2.21/0.68    inference(resolution,[],[f60,f38])).
% 2.21/0.68  fof(f60,plain,(
% 2.21/0.68    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK3))) )),
% 2.21/0.68    inference(resolution,[],[f55,f47])).
% 2.21/0.68  fof(f55,plain,(
% 2.21/0.68    r1_xboole_0(sK1,sK3)),
% 2.21/0.68    inference(resolution,[],[f34,f48])).
% 2.21/0.68  fof(f48,plain,(
% 2.21/0.68    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f24])).
% 2.21/0.68  fof(f24,plain,(
% 2.21/0.68    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.21/0.68    inference(ennf_transformation,[],[f3])).
% 2.21/0.68  fof(f3,axiom,(
% 2.21/0.68    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.21/0.68  fof(f34,plain,(
% 2.21/0.68    r1_xboole_0(sK3,sK1)),
% 2.21/0.68    inference(cnf_transformation,[],[f26])).
% 2.21/0.68  fof(f109,plain,(
% 2.21/0.68    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1)),
% 2.21/0.68    inference(superposition,[],[f42,f90])).
% 2.21/0.68  fof(f90,plain,(
% 2.21/0.68    sK1 = k4_xboole_0(sK1,sK3)),
% 2.21/0.68    inference(forward_demodulation,[],[f89,f36])).
% 2.21/0.68  fof(f89,plain,(
% 2.21/0.68    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.21/0.68    inference(superposition,[],[f43,f72])).
% 2.21/0.68  fof(f2486,plain,(
% 2.21/0.68    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(superposition,[],[f107,f372])).
% 2.21/0.68  fof(f372,plain,(
% 2.21/0.68    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f370,f185])).
% 2.21/0.68  fof(f185,plain,(
% 2.21/0.68    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(forward_demodulation,[],[f184,f32])).
% 2.21/0.68  fof(f184,plain,(
% 2.21/0.68    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(forward_demodulation,[],[f183,f41])).
% 2.21/0.68  fof(f183,plain,(
% 2.21/0.68    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(forward_demodulation,[],[f180,f45])).
% 2.21/0.68  fof(f180,plain,(
% 2.21/0.68    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 2.21/0.68    inference(superposition,[],[f45,f152])).
% 2.21/0.68  fof(f152,plain,(
% 2.21/0.68    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.21/0.68    inference(superposition,[],[f44,f32])).
% 2.21/0.68  fof(f44,plain,(
% 2.21/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f10])).
% 2.21/0.68  fof(f10,axiom,(
% 2.21/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.21/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.21/0.68  fof(f370,plain,(
% 2.21/0.68    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 2.21/0.68    inference(superposition,[],[f45,f359])).
% 2.21/0.68  fof(f359,plain,(
% 2.21/0.68    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 2.21/0.68    inference(backward_demodulation,[],[f152,f356])).
% 2.21/0.68  fof(f356,plain,(
% 2.21/0.68    sK2 = k4_xboole_0(sK2,sK3)),
% 2.21/0.68    inference(forward_demodulation,[],[f355,f36])).
% 2.21/0.68  fof(f355,plain,(
% 2.21/0.68    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3)),
% 2.21/0.68    inference(superposition,[],[f43,f350])).
% 2.21/0.68  fof(f350,plain,(
% 2.21/0.68    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 2.21/0.68    inference(resolution,[],[f349,f38])).
% 2.21/0.68  fof(f349,plain,(
% 2.21/0.68    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK2,sK3))) )),
% 2.21/0.68    inference(resolution,[],[f345,f47])).
% 2.21/0.68  fof(f345,plain,(
% 2.21/0.68    r1_xboole_0(sK2,sK3)),
% 2.21/0.68    inference(resolution,[],[f327,f48])).
% 2.21/0.68  fof(f327,plain,(
% 2.21/0.68    r1_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(subsumption_resolution,[],[f324,f63])).
% 2.21/0.68  fof(f63,plain,(
% 2.21/0.68    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.21/0.68    inference(backward_demodulation,[],[f54,f61])).
% 2.21/0.68  fof(f324,plain,(
% 2.21/0.68    r2_hidden(sK5(sK3,sK2),k1_xboole_0) | r1_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(superposition,[],[f46,f323])).
% 2.21/0.68  fof(f323,plain,(
% 2.21/0.68    k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f322,f100])).
% 2.21/0.68  fof(f100,plain,(
% 2.21/0.68    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 2.21/0.68    inference(forward_demodulation,[],[f99,f66])).
% 2.21/0.68  fof(f66,plain,(
% 2.21/0.68    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 2.21/0.68    inference(resolution,[],[f56,f38])).
% 2.21/0.68  fof(f56,plain,(
% 2.21/0.68    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK3,sK1))) )),
% 2.21/0.68    inference(resolution,[],[f34,f47])).
% 2.21/0.68  fof(f99,plain,(
% 2.21/0.68    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK3)),
% 2.21/0.68    inference(superposition,[],[f42,f82])).
% 2.21/0.68  fof(f82,plain,(
% 2.21/0.68    sK3 = k4_xboole_0(sK3,sK1)),
% 2.21/0.68    inference(forward_demodulation,[],[f81,f36])).
% 2.21/0.68  fof(f81,plain,(
% 2.21/0.68    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 2.21/0.68    inference(superposition,[],[f43,f66])).
% 2.21/0.68  fof(f322,plain,(
% 2.21/0.68    k4_xboole_0(sK3,sK3) = k3_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(superposition,[],[f42,f312])).
% 2.21/0.68  fof(f312,plain,(
% 2.21/0.68    sK3 = k4_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(forward_demodulation,[],[f302,f82])).
% 2.21/0.68  fof(f302,plain,(
% 2.21/0.68    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2)),
% 2.21/0.68    inference(superposition,[],[f97,f172])).
% 2.21/0.68  fof(f97,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 2.21/0.68    inference(superposition,[],[f51,f82])).
% 2.21/0.68  fof(f46,plain,(
% 2.21/0.68    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.21/0.68    inference(cnf_transformation,[],[f30])).
% 2.21/0.68  fof(f107,plain,(
% 2.21/0.68    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK3,X0)) = k4_xboole_0(sK1,X0)) )),
% 2.21/0.68    inference(superposition,[],[f51,f90])).
% 2.21/0.68  % SZS output end Proof for theBenchmark
% 2.21/0.68  % (16989)------------------------------
% 2.21/0.68  % (16989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.68  % (16989)Termination reason: Refutation
% 2.21/0.68  
% 2.21/0.68  % (16989)Memory used [KB]: 2686
% 2.21/0.68  % (16989)Time elapsed: 0.193 s
% 2.21/0.68  % (16989)------------------------------
% 2.21/0.68  % (16989)------------------------------
% 2.21/0.68  % (16965)Success in time 0.325 s
%------------------------------------------------------------------------------
