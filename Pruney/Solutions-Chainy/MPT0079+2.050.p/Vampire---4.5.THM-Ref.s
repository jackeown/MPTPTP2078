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
% DateTime   : Thu Dec  3 12:30:58 EST 2020

% Result     : Theorem 4.08s
% Output     : Refutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 184 expanded)
%              Number of leaves         :   19 (  55 expanded)
%              Depth                    :   17
%              Number of atoms          :  164 ( 360 expanded)
%              Number of equality atoms :   72 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6262,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6261,f4574])).

fof(f4574,plain,(
    r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f4556,f35])).

fof(f35,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27])).

fof(f27,plain,
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f4556,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f140,f521])).

fof(f521,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f495,f38])).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f495,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f56,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

% (5629)Time limit reached!
% (5629)------------------------------
% (5629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

% (5629)Termination reason: Time limit
% (5629)Termination phase: Saturation

% (5629)Memory used [KB]: 12153
% (5629)Time elapsed: 0.500 s
% (5629)------------------------------
% (5629)------------------------------
fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f31])).

fof(f31,plain,(
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
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f44,f43])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f140,plain,(
    r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f89,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f66,f34])).

fof(f34,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X1,k2_xboole_0(X1,X2)) ) ),
    inference(superposition,[],[f50,f42])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f6261,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f6211,f37])).

fof(f37,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f6211,plain,
    ( sK1 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f5838,f84])).

fof(f84,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = X2
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f79,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f79,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f46,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f5838,plain,(
    sK2 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f238,f4106])).

fof(f4106,plain,(
    sK2 = k2_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f4073,f39])).

fof(f4073,plain,(
    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f46,f4065])).

fof(f4065,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f4061,f36])).

fof(f36,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f4061,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f3646,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X1,X2),X0)
      | k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f3646,plain,(
    r1_tarski(k4_xboole_0(sK1,sK2),sK3) ),
    inference(resolution,[],[f3623,f97])).

fof(f97,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,k2_xboole_0(sK0,sK1))
      | r1_tarski(k4_xboole_0(X8,sK2),sK3) ) ),
    inference(superposition,[],[f54,f34])).

fof(f3623,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X11,X10)) ),
    inference(trivial_inequality_removal,[],[f3592])).

fof(f3592,plain,(
    ! [X10,X11] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X10,k2_xboole_0(X11,X10)) ) ),
    inference(superposition,[],[f50,f842])).

fof(f842,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(X13,k2_xboole_0(X14,X13)) ),
    inference(forward_demodulation,[],[f787,f173])).

fof(f173,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(forward_demodulation,[],[f163,f61])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f39])).

fof(f163,plain,(
    ! [X3] : k2_xboole_0(k4_xboole_0(X3,X3),X3) = X3 ),
    inference(superposition,[],[f57,f38])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f787,plain,(
    ! [X14,X13] : k1_xboole_0 = k4_xboole_0(X13,k2_xboole_0(k1_xboole_0,k2_xboole_0(X14,X13))) ),
    inference(superposition,[],[f233,f173])).

fof(f233,plain,(
    ! [X8,X7,X9] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X9,X8))) ),
    inference(superposition,[],[f42,f210])).

fof(f210,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f53,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(f238,plain,(
    ! [X10,X11] : k2_xboole_0(X11,X10) = k2_xboole_0(X10,k2_xboole_0(X11,X10)) ),
    inference(forward_demodulation,[],[f213,f173])).

fof(f213,plain,(
    ! [X10,X11] : k2_xboole_0(k1_xboole_0,k2_xboole_0(X11,X10)) = k2_xboole_0(X10,k2_xboole_0(X11,X10)) ),
    inference(superposition,[],[f210,f173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (5621)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5629)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (5639)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (5632)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (5640)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (5624)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (5622)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (5619)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (5636)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (5623)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (5620)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (5646)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5618)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (5626)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (5642)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5625)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (5627)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (5635)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (5637)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (5630)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (5641)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (5628)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (5634)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (5631)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (5644)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (5633)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (5645)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (5617)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (5643)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (5638)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 3.29/0.86  % (5622)Time limit reached!
% 3.29/0.86  % (5622)------------------------------
% 3.29/0.86  % (5622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.86  % (5622)Termination reason: Time limit
% 3.29/0.86  % (5622)Termination phase: Saturation
% 3.29/0.86  
% 3.29/0.86  % (5622)Memory used [KB]: 10362
% 3.29/0.86  % (5622)Time elapsed: 0.400 s
% 3.29/0.86  % (5622)------------------------------
% 3.29/0.86  % (5622)------------------------------
% 4.08/0.89  % (5646)Refutation found. Thanks to Tanya!
% 4.08/0.89  % SZS status Theorem for theBenchmark
% 4.08/0.90  % SZS output start Proof for theBenchmark
% 4.08/0.90  fof(f6262,plain,(
% 4.08/0.90    $false),
% 4.08/0.90    inference(subsumption_resolution,[],[f6261,f4574])).
% 4.08/0.90  fof(f4574,plain,(
% 4.08/0.90    r1_tarski(sK2,sK1)),
% 4.08/0.90    inference(subsumption_resolution,[],[f4556,f35])).
% 4.08/0.90  fof(f35,plain,(
% 4.08/0.90    r1_xboole_0(sK2,sK0)),
% 4.08/0.90    inference(cnf_transformation,[],[f28])).
% 4.08/0.90  fof(f28,plain,(
% 4.08/0.90    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 4.08/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f27])).
% 4.08/0.90  fof(f27,plain,(
% 4.08/0.90    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 4.08/0.90    introduced(choice_axiom,[])).
% 4.08/0.90  fof(f21,plain,(
% 4.08/0.90    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 4.08/0.90    inference(flattening,[],[f20])).
% 4.08/0.90  fof(f20,plain,(
% 4.08/0.90    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 4.08/0.90    inference(ennf_transformation,[],[f18])).
% 4.08/0.90  fof(f18,negated_conjecture,(
% 4.08/0.90    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 4.08/0.90    inference(negated_conjecture,[],[f17])).
% 4.08/0.90  fof(f17,conjecture,(
% 4.08/0.90    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).
% 4.08/0.90  fof(f4556,plain,(
% 4.08/0.90    r1_tarski(sK2,sK1) | ~r1_xboole_0(sK2,sK0)),
% 4.08/0.90    inference(superposition,[],[f140,f521])).
% 4.08/0.90  fof(f521,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 4.08/0.90    inference(forward_demodulation,[],[f495,f38])).
% 4.08/0.90  fof(f38,plain,(
% 4.08/0.90    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.08/0.90    inference(cnf_transformation,[],[f7])).
% 4.08/0.90  fof(f7,axiom,(
% 4.08/0.90    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 4.08/0.90  fof(f495,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k1_xboole_0) | ~r1_xboole_0(X0,X1)) )),
% 4.08/0.90    inference(superposition,[],[f56,f103])).
% 4.08/0.90  fof(f103,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 4.08/0.90    inference(resolution,[],[f58,f40])).
% 4.08/0.90  fof(f40,plain,(
% 4.08/0.90    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 4.08/0.90    inference(cnf_transformation,[],[f30])).
% 4.08/0.90  fof(f30,plain,(
% 4.08/0.90    ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0)),
% 4.08/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f29])).
% 4.08/0.90  fof(f29,plain,(
% 4.08/0.90    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 4.08/0.90    introduced(choice_axiom,[])).
% 4.08/0.90  fof(f22,plain,(
% 4.08/0.90    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 4.08/0.90    inference(ennf_transformation,[],[f2])).
% 4.08/0.90  fof(f2,axiom,(
% 4.08/0.90    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 4.08/0.90  fof(f58,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 4.08/0.90    inference(definition_unfolding,[],[f49,f43])).
% 4.08/0.90  fof(f43,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f11])).
% 4.08/0.90  % (5629)Time limit reached!
% 4.08/0.90  % (5629)------------------------------
% 4.08/0.90  % (5629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.90  fof(f11,axiom,(
% 4.08/0.90    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.08/0.90  % (5629)Termination reason: Time limit
% 4.08/0.90  % (5629)Termination phase: Saturation
% 4.08/0.90  
% 4.08/0.90  % (5629)Memory used [KB]: 12153
% 4.08/0.90  % (5629)Time elapsed: 0.500 s
% 4.08/0.90  % (5629)------------------------------
% 4.08/0.90  % (5629)------------------------------
% 4.08/0.90  fof(f49,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f32])).
% 4.08/0.90  fof(f32,plain,(
% 4.08/0.90    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.08/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f23,f31])).
% 4.08/0.90  fof(f31,plain,(
% 4.08/0.90    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 4.08/0.90    introduced(choice_axiom,[])).
% 4.08/0.90  fof(f23,plain,(
% 4.08/0.90    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 4.08/0.90    inference(ennf_transformation,[],[f19])).
% 4.08/0.90  fof(f19,plain,(
% 4.08/0.90    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.08/0.90    inference(rectify,[],[f1])).
% 4.08/0.90  fof(f1,axiom,(
% 4.08/0.90    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 4.08/0.90  fof(f56,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 4.08/0.90    inference(definition_unfolding,[],[f44,f43])).
% 4.08/0.90  fof(f44,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f10])).
% 4.08/0.90  fof(f10,axiom,(
% 4.08/0.90    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.08/0.90  fof(f140,plain,(
% 4.08/0.90    r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 4.08/0.90    inference(resolution,[],[f89,f54])).
% 4.08/0.90  fof(f54,plain,(
% 4.08/0.90    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f24])).
% 4.08/0.90  fof(f24,plain,(
% 4.08/0.90    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.08/0.90    inference(ennf_transformation,[],[f8])).
% 4.08/0.90  fof(f8,axiom,(
% 4.08/0.90    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 4.08/0.90  fof(f89,plain,(
% 4.08/0.90    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 4.08/0.90    inference(superposition,[],[f66,f34])).
% 4.08/0.90  fof(f34,plain,(
% 4.08/0.90    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 4.08/0.90    inference(cnf_transformation,[],[f28])).
% 4.08/0.90  fof(f66,plain,(
% 4.08/0.90    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X1,X2))) )),
% 4.08/0.90    inference(trivial_inequality_removal,[],[f65])).
% 4.08/0.90  fof(f65,plain,(
% 4.08/0.90    ( ! [X2,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X1,k2_xboole_0(X1,X2))) )),
% 4.08/0.90    inference(superposition,[],[f50,f42])).
% 4.08/0.90  fof(f42,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.08/0.90    inference(cnf_transformation,[],[f9])).
% 4.08/0.90  fof(f9,axiom,(
% 4.08/0.90    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 4.08/0.90  fof(f50,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f33])).
% 4.08/0.90  fof(f33,plain,(
% 4.08/0.90    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 4.08/0.90    inference(nnf_transformation,[],[f5])).
% 4.08/0.90  fof(f5,axiom,(
% 4.08/0.90    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).
% 4.08/0.90  fof(f6261,plain,(
% 4.08/0.90    ~r1_tarski(sK2,sK1)),
% 4.08/0.90    inference(subsumption_resolution,[],[f6211,f37])).
% 4.08/0.90  fof(f37,plain,(
% 4.08/0.90    sK1 != sK2),
% 4.08/0.90    inference(cnf_transformation,[],[f28])).
% 4.08/0.90  fof(f6211,plain,(
% 4.08/0.90    sK1 = sK2 | ~r1_tarski(sK2,sK1)),
% 4.08/0.90    inference(superposition,[],[f5838,f84])).
% 4.08/0.90  fof(f84,plain,(
% 4.08/0.90    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = X2 | ~r1_tarski(X1,X2)) )),
% 4.08/0.90    inference(forward_demodulation,[],[f79,f39])).
% 4.08/0.90  fof(f39,plain,(
% 4.08/0.90    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.08/0.90    inference(cnf_transformation,[],[f3])).
% 4.08/0.90  fof(f3,axiom,(
% 4.08/0.90    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 4.08/0.90    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 4.08/0.90  fof(f79,plain,(
% 4.08/0.90    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X2,k1_xboole_0) | ~r1_tarski(X1,X2)) )),
% 4.08/0.90    inference(superposition,[],[f46,f51])).
% 4.08/0.90  fof(f51,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f33])).
% 4.08/0.90  fof(f46,plain,(
% 4.08/0.90    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.08/0.90    inference(cnf_transformation,[],[f6])).
% 4.08/0.91  fof(f6,axiom,(
% 4.08/0.91    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.08/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.08/0.91  fof(f5838,plain,(
% 4.08/0.91    sK2 = k2_xboole_0(sK1,sK2)),
% 4.08/0.91    inference(superposition,[],[f238,f4106])).
% 4.08/0.91  fof(f4106,plain,(
% 4.08/0.91    sK2 = k2_xboole_0(sK2,sK1)),
% 4.08/0.91    inference(forward_demodulation,[],[f4073,f39])).
% 4.08/0.91  fof(f4073,plain,(
% 4.08/0.91    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,sK1)),
% 4.08/0.91    inference(superposition,[],[f46,f4065])).
% 4.08/0.91  fof(f4065,plain,(
% 4.08/0.91    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 4.08/0.91    inference(subsumption_resolution,[],[f4061,f36])).
% 4.08/0.91  fof(f36,plain,(
% 4.08/0.91    r1_xboole_0(sK3,sK1)),
% 4.08/0.91    inference(cnf_transformation,[],[f28])).
% 4.08/0.91  fof(f4061,plain,(
% 4.08/0.91    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~r1_xboole_0(sK3,sK1)),
% 4.08/0.91    inference(resolution,[],[f3646,f175])).
% 4.08/0.91  fof(f175,plain,(
% 4.08/0.91    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X1,X2),X0) | k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_xboole_0(X0,X1)) )),
% 4.08/0.91    inference(resolution,[],[f55,f41])).
% 4.08/0.91  fof(f41,plain,(
% 4.08/0.91    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 4.08/0.91    inference(cnf_transformation,[],[f4])).
% 4.08/0.91  fof(f4,axiom,(
% 4.08/0.91    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 4.08/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 4.08/0.91  fof(f55,plain,(
% 4.08/0.91    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 4.08/0.91    inference(cnf_transformation,[],[f26])).
% 4.08/0.91  fof(f26,plain,(
% 4.08/0.91    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 4.08/0.91    inference(flattening,[],[f25])).
% 4.08/0.91  fof(f25,plain,(
% 4.08/0.91    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 4.08/0.91    inference(ennf_transformation,[],[f15])).
% 4.08/0.91  fof(f15,axiom,(
% 4.08/0.91    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 4.08/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 4.08/0.91  fof(f3646,plain,(
% 4.08/0.91    r1_tarski(k4_xboole_0(sK1,sK2),sK3)),
% 4.08/0.91    inference(resolution,[],[f3623,f97])).
% 4.08/0.91  fof(f97,plain,(
% 4.08/0.91    ( ! [X8] : (~r1_tarski(X8,k2_xboole_0(sK0,sK1)) | r1_tarski(k4_xboole_0(X8,sK2),sK3)) )),
% 4.08/0.91    inference(superposition,[],[f54,f34])).
% 4.08/0.91  fof(f3623,plain,(
% 4.08/0.91    ( ! [X10,X11] : (r1_tarski(X10,k2_xboole_0(X11,X10))) )),
% 4.08/0.91    inference(trivial_inequality_removal,[],[f3592])).
% 4.08/0.91  fof(f3592,plain,(
% 4.08/0.91    ( ! [X10,X11] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X10,k2_xboole_0(X11,X10))) )),
% 4.08/0.91    inference(superposition,[],[f50,f842])).
% 4.08/0.91  fof(f842,plain,(
% 4.08/0.91    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(X13,k2_xboole_0(X14,X13))) )),
% 4.08/0.91    inference(forward_demodulation,[],[f787,f173])).
% 4.08/0.91  fof(f173,plain,(
% 4.08/0.91    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) )),
% 4.08/0.91    inference(forward_demodulation,[],[f163,f61])).
% 4.08/0.91  fof(f61,plain,(
% 4.08/0.91    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 4.08/0.91    inference(superposition,[],[f42,f39])).
% 4.08/0.91  fof(f163,plain,(
% 4.08/0.91    ( ! [X3] : (k2_xboole_0(k4_xboole_0(X3,X3),X3) = X3) )),
% 4.08/0.91    inference(superposition,[],[f57,f38])).
% 4.08/0.91  fof(f57,plain,(
% 4.08/0.91    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 4.08/0.91    inference(definition_unfolding,[],[f47,f43])).
% 4.08/0.91  fof(f47,plain,(
% 4.08/0.91    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 4.08/0.91    inference(cnf_transformation,[],[f13])).
% 4.08/0.91  fof(f13,axiom,(
% 4.08/0.91    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 4.08/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 4.08/0.91  fof(f787,plain,(
% 4.08/0.91    ( ! [X14,X13] : (k1_xboole_0 = k4_xboole_0(X13,k2_xboole_0(k1_xboole_0,k2_xboole_0(X14,X13)))) )),
% 4.08/0.91    inference(superposition,[],[f233,f173])).
% 4.08/0.91  fof(f233,plain,(
% 4.08/0.91    ( ! [X8,X7,X9] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X7,X8),k2_xboole_0(X7,k2_xboole_0(X9,X8)))) )),
% 4.08/0.91    inference(superposition,[],[f42,f210])).
% 4.08/0.91  fof(f210,plain,(
% 4.08/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 4.08/0.91    inference(forward_demodulation,[],[f53,f52])).
% 4.08/0.91  fof(f52,plain,(
% 4.08/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.08/0.91    inference(cnf_transformation,[],[f12])).
% 4.08/0.91  fof(f12,axiom,(
% 4.08/0.91    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.08/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.08/0.91  fof(f53,plain,(
% 4.08/0.91    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 4.08/0.91    inference(cnf_transformation,[],[f14])).
% 4.08/0.91  fof(f14,axiom,(
% 4.08/0.91    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 4.08/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).
% 4.08/0.91  fof(f238,plain,(
% 4.08/0.91    ( ! [X10,X11] : (k2_xboole_0(X11,X10) = k2_xboole_0(X10,k2_xboole_0(X11,X10))) )),
% 4.08/0.91    inference(forward_demodulation,[],[f213,f173])).
% 4.08/0.91  fof(f213,plain,(
% 4.08/0.91    ( ! [X10,X11] : (k2_xboole_0(k1_xboole_0,k2_xboole_0(X11,X10)) = k2_xboole_0(X10,k2_xboole_0(X11,X10))) )),
% 4.08/0.91    inference(superposition,[],[f210,f173])).
% 4.08/0.91  % SZS output end Proof for theBenchmark
% 4.08/0.91  % (5646)------------------------------
% 4.08/0.91  % (5646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/0.91  % (5646)Termination reason: Refutation
% 4.08/0.91  
% 4.08/0.91  % (5646)Memory used [KB]: 5245
% 4.08/0.91  % (5646)Time elapsed: 0.467 s
% 4.08/0.91  % (5646)------------------------------
% 4.08/0.91  % (5646)------------------------------
% 4.08/0.91  % (5616)Success in time 0.548 s
%------------------------------------------------------------------------------
