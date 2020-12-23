%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:55 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  146 (2018 expanded)
%              Number of leaves         :   14 ( 564 expanded)
%              Depth                    :   51
%              Number of atoms          :  211 (5504 expanded)
%              Number of equality atoms :  131 (2356 expanded)
%              Maximal formula depth    :    9 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(subsumption_resolution,[],[f902,f28])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f20])).

fof(f20,plain,
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

fof(f902,plain,(
    sK1 = sK2 ),
    inference(backward_demodulation,[],[f412,f901])).

fof(f901,plain,(
    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(forward_demodulation,[],[f890,f186])).

fof(f186,plain,(
    sK1 = k4_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f184,f30])).

fof(f30,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f184,plain,(
    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f34,f181])).

fof(f181,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f180,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f180,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( r1_xboole_0(sK1,sK3)
    | r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f106,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK3),sK1)
      | r1_xboole_0(X0,sK3) ) ),
    inference(resolution,[],[f47,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f890,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f36,f840])).

fof(f840,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f839,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f839,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK3) ),
    inference(forward_demodulation,[],[f838,f489])).

fof(f489,plain,(
    sK0 = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f488,f144])).

fof(f144,plain,(
    sK0 = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f143,f31])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f143,plain,(
    k2_xboole_0(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f141,f32])).

fof(f141,plain,(
    k2_xboole_0(sK0,sK0) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f35,f139])).

fof(f139,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f138,f131])).

fof(f131,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f130,f40])).

fof(f130,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( r1_xboole_0(sK0,sK2)
    | r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f104,f37])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK2),sK0)
      | r1_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f26,f39])).

fof(f26,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f138,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f33,f136])).

fof(f136,plain,(
    sK0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f134,f30])).

fof(f134,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f34,f131])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f488,plain,(
    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK0,sK3) ),
    inference(forward_demodulation,[],[f486,f32])).

fof(f486,plain,(
    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3) ),
    inference(superposition,[],[f35,f484])).

fof(f484,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK0) ),
    inference(backward_demodulation,[],[f310,f483])).

fof(f483,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f482,f332])).

fof(f332,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f325,f56])).

fof(f56,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f42,f51])).

fof(f51,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(forward_demodulation,[],[f49,f30])).

fof(f49,plain,(
    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f34,f44])).

fof(f44,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f26,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f325,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f316,f82])).

fof(f82,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f81,f61])).

fof(f61,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(forward_demodulation,[],[f60,f46])).

fof(f46,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f27,f40])).

fof(f60,plain,(
    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(forward_demodulation,[],[f53,f30])).

fof(f53,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f34,f46])).

fof(f81,plain,(
    k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,sK3) ),
    inference(superposition,[],[f36,f72])).

fof(f72,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f71,f31])).

fof(f71,plain,(
    k2_xboole_0(sK3,sK3) = k2_xboole_0(k1_xboole_0,sK3) ),
    inference(forward_demodulation,[],[f69,f32])).

fof(f69,plain,(
    k2_xboole_0(sK3,sK3) = k2_xboole_0(sK3,k1_xboole_0) ),
    inference(superposition,[],[f35,f61])).

fof(f316,plain,(
    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f62,f25])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f42,f58])).

fof(f58,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f57,f44])).

fof(f57,plain,(
    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2) ),
    inference(superposition,[],[f33,f51])).

fof(f482,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f478,f56])).

fof(f478,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f36,f429])).

fof(f429,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f424,f347])).

fof(f347,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f346,f194])).

fof(f194,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f193,f31])).

fof(f193,plain,(
    k2_xboole_0(sK1,sK1) = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f191,f32])).

fof(f191,plain,(
    k2_xboole_0(sK1,sK1) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f35,f189])).

fof(f189,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f188,f181])).

fof(f188,plain,(
    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f33,f186])).

fof(f346,plain,(
    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f344,f32])).

fof(f344,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f35,f332])).

fof(f424,plain,(
    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f128,f421])).

fof(f421,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f419,f174])).

fof(f174,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f173,f25])).

fof(f173,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f172,f32])).

fof(f172,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f169,f35])).

fof(f169,plain,(
    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3)) ),
    inference(superposition,[],[f35,f127])).

fof(f127,plain,(
    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(superposition,[],[f36,f25])).

fof(f419,plain,(
    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f35,f412])).

fof(f128,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f126,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f126,plain,(
    ! [X0] : k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0) ),
    inference(superposition,[],[f43,f25])).

fof(f310,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,sK0) ),
    inference(backward_demodulation,[],[f285,f304])).

fof(f304,plain,(
    ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f59,f32])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f42,f55])).

fof(f285,plain,(
    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f36,f174])).

fof(f838,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3)) ),
    inference(forward_demodulation,[],[f831,f32])).

fof(f831,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK0)) ),
    inference(superposition,[],[f799,f43])).

fof(f799,plain,(
    k2_xboole_0(sK1,sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK0) ),
    inference(forward_demodulation,[],[f798,f196])).

fof(f196,plain,(
    ! [X0] : k2_xboole_0(sK1,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f43,f194])).

fof(f798,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f795,f32])).

fof(f795,plain,(
    k2_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0) ),
    inference(superposition,[],[f35,f787])).

fof(f787,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f786,f332])).

fof(f786,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k4_xboole_0(sK2,sK1) ),
    inference(backward_demodulation,[],[f288,f776])).

fof(f776,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f416,f32])).

fof(f416,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) ),
    inference(backward_demodulation,[],[f171,f413])).

fof(f413,plain,(
    ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f42,f410])).

fof(f410,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(forward_demodulation,[],[f408,f30])).

fof(f408,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3) ),
    inference(superposition,[],[f34,f405])).

fof(f405,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f404,f40])).

fof(f404,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,
    ( r1_xboole_0(sK2,sK3)
    | r1_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f372,f37])).

fof(f372,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,sK3),sK2)
      | r1_xboole_0(X0,sK3) ) ),
    inference(resolution,[],[f365,f38])).

fof(f365,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f362,f39])).

fof(f362,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f360])).

fof(f360,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f41,f359])).

fof(f359,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f358,f61])).

fof(f358,plain,(
    k4_xboole_0(sK3,sK3) = k3_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f33,f356])).

fof(f356,plain,(
    sK3 = k4_xboole_0(sK3,sK2) ),
    inference(forward_demodulation,[],[f354,f55])).

fof(f354,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2) ),
    inference(superposition,[],[f59,f347])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f171,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f168,f42])).

fof(f168,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0) ),
    inference(superposition,[],[f42,f127])).

fof(f288,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f36,f266])).

fof(f266,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f260,f25])).

fof(f260,plain,(
    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f128,f31])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f412,plain,(
    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) ),
    inference(backward_demodulation,[],[f127,f410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (22616)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (22640)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (22624)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (22612)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (22614)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (22615)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (22618)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (22638)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.54  % (22639)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (22642)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.54  % (22641)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.54  % (22627)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (22637)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.54  % (22636)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (22627)Refutation not found, incomplete strategy% (22627)------------------------------
% 1.31/0.54  % (22627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (22617)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (22613)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (22635)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.54  % (22627)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (22627)Memory used [KB]: 6140
% 1.31/0.54  % (22627)Time elapsed: 0.080 s
% 1.31/0.54  % (22627)------------------------------
% 1.31/0.54  % (22627)------------------------------
% 1.31/0.54  % (22631)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.54  % (22619)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.54  % (22632)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.55  % (22628)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (22634)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (22629)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (22620)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (22629)Refutation not found, incomplete strategy% (22629)------------------------------
% 1.45/0.55  % (22629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (22629)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (22629)Memory used [KB]: 10618
% 1.45/0.55  % (22629)Time elapsed: 0.149 s
% 1.45/0.55  % (22629)------------------------------
% 1.45/0.55  % (22629)------------------------------
% 1.45/0.56  % (22621)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.56  % (22622)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.56  % (22623)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.56  % (22625)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (22633)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.56  % (22626)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.59  % (22636)Refutation found. Thanks to Tanya!
% 1.45/0.59  % SZS status Theorem for theBenchmark
% 1.45/0.59  % SZS output start Proof for theBenchmark
% 1.45/0.59  fof(f903,plain,(
% 1.45/0.59    $false),
% 1.45/0.59    inference(subsumption_resolution,[],[f902,f28])).
% 1.45/0.59  fof(f28,plain,(
% 1.45/0.59    sK1 != sK2),
% 1.45/0.59    inference(cnf_transformation,[],[f21])).
% 1.45/0.59  fof(f21,plain,(
% 1.45/0.59    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.45/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f20])).
% 1.45/0.59  fof(f20,plain,(
% 1.45/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f18,plain,(
% 1.45/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.45/0.59    inference(flattening,[],[f17])).
% 1.45/0.59  fof(f17,plain,(
% 1.45/0.59    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.45/0.59    inference(ennf_transformation,[],[f14])).
% 1.45/0.59  fof(f14,negated_conjecture,(
% 1.45/0.59    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.45/0.59    inference(negated_conjecture,[],[f13])).
% 1.45/0.59  fof(f13,conjecture,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.45/0.59  fof(f902,plain,(
% 1.45/0.59    sK1 = sK2),
% 1.45/0.59    inference(backward_demodulation,[],[f412,f901])).
% 1.45/0.59  fof(f901,plain,(
% 1.45/0.59    sK1 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.45/0.59    inference(forward_demodulation,[],[f890,f186])).
% 1.45/0.59  fof(f186,plain,(
% 1.45/0.59    sK1 = k4_xboole_0(sK1,sK3)),
% 1.45/0.59    inference(forward_demodulation,[],[f184,f30])).
% 1.45/0.59  fof(f30,plain,(
% 1.45/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.59    inference(cnf_transformation,[],[f7])).
% 1.45/0.59  fof(f7,axiom,(
% 1.45/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.45/0.59  fof(f184,plain,(
% 1.45/0.59    k4_xboole_0(sK1,sK3) = k4_xboole_0(sK1,k1_xboole_0)),
% 1.45/0.59    inference(superposition,[],[f34,f181])).
% 1.45/0.59  fof(f181,plain,(
% 1.45/0.59    k1_xboole_0 = k3_xboole_0(sK1,sK3)),
% 1.45/0.59    inference(resolution,[],[f180,f40])).
% 1.45/0.59  fof(f40,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f24])).
% 1.45/0.59  fof(f24,plain,(
% 1.45/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(nnf_transformation,[],[f2])).
% 1.45/0.59  fof(f2,axiom,(
% 1.45/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.45/0.59  fof(f180,plain,(
% 1.45/0.59    r1_xboole_0(sK1,sK3)),
% 1.45/0.59    inference(duplicate_literal_removal,[],[f179])).
% 1.45/0.59  fof(f179,plain,(
% 1.45/0.59    r1_xboole_0(sK1,sK3) | r1_xboole_0(sK1,sK3)),
% 1.45/0.59    inference(resolution,[],[f106,f37])).
% 1.45/0.59  fof(f37,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f23])).
% 1.45/0.59  fof(f23,plain,(
% 1.45/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f22])).
% 1.45/0.59  fof(f22,plain,(
% 1.45/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.45/0.59    introduced(choice_axiom,[])).
% 1.45/0.59  fof(f19,plain,(
% 1.45/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(ennf_transformation,[],[f16])).
% 1.45/0.59  fof(f16,plain,(
% 1.45/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.59    inference(rectify,[],[f4])).
% 1.45/0.59  fof(f4,axiom,(
% 1.45/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.59  fof(f106,plain,(
% 1.45/0.59    ( ! [X0] : (~r2_hidden(sK4(X0,sK3),sK1) | r1_xboole_0(X0,sK3)) )),
% 1.45/0.59    inference(resolution,[],[f47,f38])).
% 1.45/0.59  fof(f38,plain,(
% 1.45/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f23])).
% 1.45/0.59  fof(f47,plain,(
% 1.45/0.59    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK1)) )),
% 1.45/0.59    inference(resolution,[],[f27,f39])).
% 1.45/0.59  fof(f39,plain,(
% 1.45/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f23])).
% 1.45/0.59  fof(f27,plain,(
% 1.45/0.59    r1_xboole_0(sK3,sK1)),
% 1.45/0.59    inference(cnf_transformation,[],[f21])).
% 1.45/0.59  fof(f34,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f10])).
% 1.45/0.59  fof(f10,axiom,(
% 1.45/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.45/0.59  fof(f890,plain,(
% 1.45/0.59    k4_xboole_0(k2_xboole_0(sK0,sK1),sK3) = k4_xboole_0(sK1,sK3)),
% 1.45/0.59    inference(superposition,[],[f36,f840])).
% 1.45/0.59  fof(f840,plain,(
% 1.45/0.59    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK1,sK3)),
% 1.45/0.59    inference(forward_demodulation,[],[f839,f32])).
% 1.45/0.59  fof(f32,plain,(
% 1.45/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f1])).
% 1.45/0.60  fof(f1,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.45/0.60  fof(f839,plain,(
% 1.45/0.60    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f838,f489])).
% 1.45/0.60  fof(f489,plain,(
% 1.45/0.60    sK0 = k2_xboole_0(sK0,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f488,f144])).
% 1.45/0.60  fof(f144,plain,(
% 1.45/0.60    sK0 = k2_xboole_0(k1_xboole_0,sK0)),
% 1.45/0.60    inference(forward_demodulation,[],[f143,f31])).
% 1.45/0.60  fof(f31,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f15])).
% 1.45/0.60  fof(f15,plain,(
% 1.45/0.60    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.45/0.60    inference(rectify,[],[f3])).
% 1.45/0.60  fof(f3,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.45/0.60  fof(f143,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK0) = k2_xboole_0(k1_xboole_0,sK0)),
% 1.45/0.60    inference(forward_demodulation,[],[f141,f32])).
% 1.45/0.60  fof(f141,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK0) = k2_xboole_0(sK0,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f35,f139])).
% 1.45/0.60  fof(f139,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 1.45/0.60    inference(forward_demodulation,[],[f138,f131])).
% 1.45/0.60  fof(f131,plain,(
% 1.45/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 1.45/0.60    inference(resolution,[],[f130,f40])).
% 1.45/0.60  fof(f130,plain,(
% 1.45/0.60    r1_xboole_0(sK0,sK2)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f129])).
% 1.45/0.60  fof(f129,plain,(
% 1.45/0.60    r1_xboole_0(sK0,sK2) | r1_xboole_0(sK0,sK2)),
% 1.45/0.60    inference(resolution,[],[f104,f37])).
% 1.45/0.60  fof(f104,plain,(
% 1.45/0.60    ( ! [X0] : (~r2_hidden(sK4(X0,sK2),sK0) | r1_xboole_0(X0,sK2)) )),
% 1.45/0.60    inference(resolution,[],[f45,f38])).
% 1.45/0.60  fof(f45,plain,(
% 1.45/0.60    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) )),
% 1.45/0.60    inference(resolution,[],[f26,f39])).
% 1.45/0.60  fof(f26,plain,(
% 1.45/0.60    r1_xboole_0(sK2,sK0)),
% 1.45/0.60    inference(cnf_transformation,[],[f21])).
% 1.45/0.60  fof(f138,plain,(
% 1.45/0.60    k3_xboole_0(sK0,sK2) = k4_xboole_0(sK0,sK0)),
% 1.45/0.60    inference(superposition,[],[f33,f136])).
% 1.45/0.60  fof(f136,plain,(
% 1.45/0.60    sK0 = k4_xboole_0(sK0,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f134,f30])).
% 1.45/0.60  fof(f134,plain,(
% 1.45/0.60    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f34,f131])).
% 1.45/0.60  fof(f33,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f11])).
% 1.45/0.60  fof(f11,axiom,(
% 1.45/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.45/0.60  fof(f35,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f6])).
% 1.45/0.60  fof(f6,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.45/0.60  fof(f488,plain,(
% 1.45/0.60    k2_xboole_0(k1_xboole_0,sK0) = k2_xboole_0(sK0,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f486,f32])).
% 1.45/0.60  fof(f486,plain,(
% 1.45/0.60    k2_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(sK0,sK3)),
% 1.45/0.60    inference(superposition,[],[f35,f484])).
% 1.45/0.60  fof(f484,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK3,sK0)),
% 1.45/0.60    inference(backward_demodulation,[],[f310,f483])).
% 1.45/0.60  fof(f483,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(forward_demodulation,[],[f482,f332])).
% 1.45/0.60  fof(f332,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.45/0.60    inference(superposition,[],[f325,f56])).
% 1.45/0.60  fof(f56,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.45/0.60    inference(superposition,[],[f42,f51])).
% 1.45/0.60  fof(f51,plain,(
% 1.45/0.60    sK2 = k4_xboole_0(sK2,sK0)),
% 1.45/0.60    inference(forward_demodulation,[],[f49,f30])).
% 1.45/0.60  fof(f49,plain,(
% 1.45/0.60    k4_xboole_0(sK2,sK0) = k4_xboole_0(sK2,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f34,f44])).
% 1.45/0.60  fof(f44,plain,(
% 1.45/0.60    k1_xboole_0 = k3_xboole_0(sK2,sK0)),
% 1.45/0.60    inference(resolution,[],[f26,f40])).
% 1.45/0.60  fof(f42,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f9])).
% 1.45/0.60  fof(f9,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.45/0.60  fof(f325,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(forward_demodulation,[],[f316,f82])).
% 1.45/0.60  fof(f82,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f81,f61])).
% 1.45/0.60  fof(f61,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f60,f46])).
% 1.45/0.60  fof(f46,plain,(
% 1.45/0.60    k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 1.45/0.60    inference(resolution,[],[f27,f40])).
% 1.45/0.60  fof(f60,plain,(
% 1.45/0.60    k3_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK3)),
% 1.45/0.60    inference(superposition,[],[f33,f55])).
% 1.45/0.60  fof(f55,plain,(
% 1.45/0.60    sK3 = k4_xboole_0(sK3,sK1)),
% 1.45/0.60    inference(forward_demodulation,[],[f53,f30])).
% 1.45/0.60  fof(f53,plain,(
% 1.45/0.60    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f34,f46])).
% 1.45/0.60  fof(f81,plain,(
% 1.45/0.60    k4_xboole_0(sK3,sK3) = k4_xboole_0(k1_xboole_0,sK3)),
% 1.45/0.60    inference(superposition,[],[f36,f72])).
% 1.45/0.60  fof(f72,plain,(
% 1.45/0.60    sK3 = k2_xboole_0(k1_xboole_0,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f71,f31])).
% 1.45/0.60  fof(f71,plain,(
% 1.45/0.60    k2_xboole_0(sK3,sK3) = k2_xboole_0(k1_xboole_0,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f69,f32])).
% 1.45/0.60  fof(f69,plain,(
% 1.45/0.60    k2_xboole_0(sK3,sK3) = k2_xboole_0(sK3,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f35,f61])).
% 1.45/0.60  fof(f316,plain,(
% 1.45/0.60    k4_xboole_0(k1_xboole_0,sK3) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(superposition,[],[f62,f25])).
% 1.45/0.60  fof(f25,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(cnf_transformation,[],[f21])).
% 1.45/0.60  fof(f62,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK2,X0)) = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.45/0.60    inference(superposition,[],[f42,f58])).
% 1.45/0.60  fof(f58,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f57,f44])).
% 1.45/0.60  fof(f57,plain,(
% 1.45/0.60    k3_xboole_0(sK2,sK0) = k4_xboole_0(sK2,sK2)),
% 1.45/0.60    inference(superposition,[],[f33,f51])).
% 1.45/0.60  fof(f482,plain,(
% 1.45/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,sK1)),
% 1.45/0.60    inference(forward_demodulation,[],[f478,f56])).
% 1.45/0.60  fof(f478,plain,(
% 1.45/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(superposition,[],[f36,f429])).
% 1.45/0.60  fof(f429,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(forward_demodulation,[],[f424,f347])).
% 1.45/0.60  fof(f347,plain,(
% 1.45/0.60    sK1 = k2_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f346,f194])).
% 1.45/0.60  fof(f194,plain,(
% 1.45/0.60    sK1 = k2_xboole_0(k1_xboole_0,sK1)),
% 1.45/0.60    inference(forward_demodulation,[],[f193,f31])).
% 1.45/0.60  fof(f193,plain,(
% 1.45/0.60    k2_xboole_0(sK1,sK1) = k2_xboole_0(k1_xboole_0,sK1)),
% 1.45/0.60    inference(forward_demodulation,[],[f191,f32])).
% 1.45/0.60  fof(f191,plain,(
% 1.45/0.60    k2_xboole_0(sK1,sK1) = k2_xboole_0(sK1,k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f35,f189])).
% 1.45/0.60  fof(f189,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.45/0.60    inference(forward_demodulation,[],[f188,f181])).
% 1.45/0.60  fof(f188,plain,(
% 1.45/0.60    k3_xboole_0(sK1,sK3) = k4_xboole_0(sK1,sK1)),
% 1.45/0.60    inference(superposition,[],[f33,f186])).
% 1.45/0.60  fof(f346,plain,(
% 1.45/0.60    k2_xboole_0(k1_xboole_0,sK1) = k2_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f344,f32])).
% 1.45/0.60  fof(f344,plain,(
% 1.45/0.60    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(superposition,[],[f35,f332])).
% 1.45/0.60  fof(f424,plain,(
% 1.45/0.60    k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.45/0.60    inference(superposition,[],[f128,f421])).
% 1.45/0.60  fof(f421,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f419,f174])).
% 1.45/0.60  fof(f174,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(forward_demodulation,[],[f173,f25])).
% 1.45/0.60  fof(f173,plain,(
% 1.45/0.60    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(forward_demodulation,[],[f172,f32])).
% 1.45/0.60  fof(f172,plain,(
% 1.45/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(forward_demodulation,[],[f169,f35])).
% 1.45/0.60  fof(f169,plain,(
% 1.45/0.60    k2_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k2_xboole_0(sK3,k4_xboole_0(sK2,sK3))),
% 1.45/0.60    inference(superposition,[],[f35,f127])).
% 1.45/0.60  fof(f127,plain,(
% 1.45/0.60    k4_xboole_0(sK2,sK3) = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.45/0.60    inference(superposition,[],[f36,f25])).
% 1.45/0.60  fof(f419,plain,(
% 1.45/0.60    k2_xboole_0(sK3,sK2) = k2_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(superposition,[],[f35,f412])).
% 1.45/0.60  fof(f128,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK0,k2_xboole_0(sK1,X0))) )),
% 1.45/0.60    inference(forward_demodulation,[],[f126,f43])).
% 1.45/0.60  fof(f43,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f12])).
% 1.45/0.60  fof(f12,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.45/0.60  fof(f126,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(k2_xboole_0(sK0,sK1),X0)) )),
% 1.45/0.60    inference(superposition,[],[f43,f25])).
% 1.45/0.60  fof(f310,plain,(
% 1.45/0.60    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) = k4_xboole_0(sK3,sK0)),
% 1.45/0.60    inference(backward_demodulation,[],[f285,f304])).
% 1.45/0.60  fof(f304,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(X0,sK1))) )),
% 1.45/0.60    inference(superposition,[],[f59,f32])).
% 1.45/0.60  fof(f59,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 1.45/0.60    inference(superposition,[],[f42,f55])).
% 1.45/0.60  fof(f285,plain,(
% 1.45/0.60    k4_xboole_0(sK3,k2_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 1.45/0.60    inference(superposition,[],[f36,f174])).
% 1.45/0.60  fof(f838,plain,(
% 1.45/0.60    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK3))),
% 1.45/0.60    inference(forward_demodulation,[],[f831,f32])).
% 1.45/0.60  fof(f831,plain,(
% 1.45/0.60    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k2_xboole_0(sK3,sK0))),
% 1.45/0.60    inference(superposition,[],[f799,f43])).
% 1.45/0.60  fof(f799,plain,(
% 1.45/0.60    k2_xboole_0(sK1,sK3) = k2_xboole_0(k2_xboole_0(sK1,sK3),sK0)),
% 1.45/0.60    inference(forward_demodulation,[],[f798,f196])).
% 1.45/0.60  fof(f196,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(sK1,X0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,X0))) )),
% 1.45/0.60    inference(superposition,[],[f43,f194])).
% 1.45/0.60  fof(f798,plain,(
% 1.45/0.60    k2_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(sK1,sK3))),
% 1.45/0.60    inference(forward_demodulation,[],[f795,f32])).
% 1.45/0.60  fof(f795,plain,(
% 1.45/0.60    k2_xboole_0(k2_xboole_0(sK1,sK3),sK0) = k2_xboole_0(k2_xboole_0(sK1,sK3),k1_xboole_0)),
% 1.45/0.60    inference(superposition,[],[f35,f787])).
% 1.45/0.60  fof(f787,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 1.45/0.60    inference(forward_demodulation,[],[f786,f332])).
% 1.45/0.60  fof(f786,plain,(
% 1.45/0.60    k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k4_xboole_0(sK2,sK1)),
% 1.45/0.60    inference(backward_demodulation,[],[f288,f776])).
% 1.45/0.60  fof(f776,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(X0,sK3))) )),
% 1.45/0.60    inference(superposition,[],[f416,f32])).
% 1.45/0.60  fof(f416,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0))) )),
% 1.45/0.60    inference(backward_demodulation,[],[f171,f413])).
% 1.45/0.60  fof(f413,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0))) )),
% 1.45/0.60    inference(superposition,[],[f42,f410])).
% 1.45/0.60  fof(f410,plain,(
% 1.45/0.60    sK2 = k4_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(forward_demodulation,[],[f408,f30])).
% 1.45/0.60  fof(f408,plain,(
% 1.45/0.60    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(superposition,[],[f34,f405])).
% 1.45/0.60  fof(f405,plain,(
% 1.45/0.60    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(resolution,[],[f404,f40])).
% 1.45/0.60  fof(f404,plain,(
% 1.45/0.60    r1_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(duplicate_literal_removal,[],[f403])).
% 1.45/0.60  fof(f403,plain,(
% 1.45/0.60    r1_xboole_0(sK2,sK3) | r1_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(resolution,[],[f372,f37])).
% 1.45/0.60  fof(f372,plain,(
% 1.45/0.60    ( ! [X0] : (~r2_hidden(sK4(X0,sK3),sK2) | r1_xboole_0(X0,sK3)) )),
% 1.45/0.60    inference(resolution,[],[f365,f38])).
% 1.45/0.60  fof(f365,plain,(
% 1.45/0.60    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r2_hidden(X0,sK2)) )),
% 1.45/0.60    inference(resolution,[],[f362,f39])).
% 1.45/0.60  fof(f362,plain,(
% 1.45/0.60    r1_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(trivial_inequality_removal,[],[f360])).
% 1.45/0.60  fof(f360,plain,(
% 1.45/0.60    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(superposition,[],[f41,f359])).
% 1.45/0.60  fof(f359,plain,(
% 1.45/0.60    k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f358,f61])).
% 1.45/0.60  fof(f358,plain,(
% 1.45/0.60    k4_xboole_0(sK3,sK3) = k3_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(superposition,[],[f33,f356])).
% 1.45/0.60  fof(f356,plain,(
% 1.45/0.60    sK3 = k4_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f354,f55])).
% 1.45/0.60  fof(f354,plain,(
% 1.45/0.60    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,sK2)),
% 1.45/0.60    inference(superposition,[],[f59,f347])).
% 1.45/0.60  fof(f41,plain,(
% 1.45/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f24])).
% 1.45/0.60  fof(f171,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(sK2,k2_xboole_0(sK3,X0))) )),
% 1.45/0.60    inference(forward_demodulation,[],[f168,f42])).
% 1.45/0.60  fof(f168,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK3,X0)) = k4_xboole_0(k4_xboole_0(sK2,sK3),X0)) )),
% 1.45/0.60    inference(superposition,[],[f42,f127])).
% 1.45/0.60  fof(f288,plain,(
% 1.45/0.60    k4_xboole_0(sK0,k2_xboole_0(sK1,sK3)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK3))),
% 1.45/0.60    inference(superposition,[],[f36,f266])).
% 1.45/0.60  fof(f266,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 1.45/0.60    inference(forward_demodulation,[],[f260,f25])).
% 1.45/0.60  fof(f260,plain,(
% 1.45/0.60    k2_xboole_0(sK2,sK3) = k2_xboole_0(sK0,k2_xboole_0(sK1,sK3))),
% 1.45/0.60    inference(superposition,[],[f128,f31])).
% 1.45/0.60  fof(f36,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f8])).
% 1.45/0.60  fof(f8,axiom,(
% 1.45/0.60    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.45/0.60  fof(f412,plain,(
% 1.45/0.60    sK2 = k4_xboole_0(k2_xboole_0(sK0,sK1),sK3)),
% 1.45/0.60    inference(backward_demodulation,[],[f127,f410])).
% 1.45/0.60  % SZS output end Proof for theBenchmark
% 1.45/0.60  % (22636)------------------------------
% 1.45/0.60  % (22636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (22636)Termination reason: Refutation
% 1.45/0.60  
% 1.45/0.60  % (22636)Memory used [KB]: 2302
% 1.45/0.60  % (22636)Time elapsed: 0.177 s
% 1.45/0.60  % (22636)------------------------------
% 1.45/0.60  % (22636)------------------------------
% 1.45/0.60  % (22608)Success in time 0.232 s
%------------------------------------------------------------------------------
