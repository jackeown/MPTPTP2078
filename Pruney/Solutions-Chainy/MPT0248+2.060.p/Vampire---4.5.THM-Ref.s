%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:57 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  124 (5180 expanded)
%              Number of leaves         :   20 (1452 expanded)
%              Depth                    :   32
%              Number of atoms          :  258 (17125 expanded)
%              Number of equality atoms :  127 (11491 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2480,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2479,f1177])).

fof(f1177,plain,(
    k1_xboole_0 != sK1 ),
    inference(superposition,[],[f842,f1173])).

fof(f1173,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1168,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1168,plain,(
    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f61,f1099])).

fof(f1099,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f1096,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1096,plain,(
    v1_xboole_0(k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f1090,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f1090,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f1089,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f1089,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1088,f714])).

fof(f714,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f712,f254])).

fof(f254,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f252,f53])).

fof(f252,plain,
    ( v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f250,f55])).

fof(f250,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK1 = k1_tarski(sK0) ) ),
    inference(forward_demodulation,[],[f249,f83])).

fof(f83,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f80,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f80,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f56,f46])).

fof(f46,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f249,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0)))
      | sK1 = k1_tarski(sK0) ) ),
    inference(forward_demodulation,[],[f248,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f248,plain,(
    ! [X0] :
      ( sK1 = k1_tarski(sK0)
      | ~ r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1)) ) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f142,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f142,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f712,plain,
    ( k1_xboole_0 != sK1
    | sK1 = k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f676])).

fof(f676,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | sK1 = k1_tarski(sK0) ),
    inference(superposition,[],[f48,f660])).

fof(f660,plain,
    ( sK2 = k1_tarski(sK0)
    | sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f650,f252])).

fof(f650,plain,
    ( sK2 = k1_tarski(sK0)
    | ~ v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f235,f251])).

fof(f251,plain,
    ( r1_tarski(sK1,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f250,f141])).

fof(f141,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f112,f55])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f106,f53])).

fof(f106,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f57,f94])).

fof(f94,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1) ),
    inference(resolution,[],[f91,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f91,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f57,f82])).

fof(f82,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f80,f69])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f235,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | sK2 = k1_tarski(sK0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f228,f53])).

fof(f228,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | sK2 = k1_tarski(sK0) ),
    inference(superposition,[],[f152,f50])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f152,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,k3_xboole_0(sK2,X0))
      | sK2 = k1_tarski(sK0) ) ),
    inference(resolution,[],[f77,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f77,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(superposition,[],[f46,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f48,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f1088,plain,(
    r1_xboole_0(k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f1087,f64])).

fof(f1087,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f1085,f720])).

fof(f720,plain,(
    r1_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f80,f714])).

fof(f1085,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r2_hidden(sK0,sK2) ),
    inference(superposition,[],[f847,f714])).

fof(f847,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,k1_tarski(X3))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(subsumption_resolution,[],[f746,f838])).

fof(f838,plain,(
    sK1 != sK2 ),
    inference(forward_demodulation,[],[f837,f714])).

fof(f837,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(trivial_inequality_removal,[],[f716])).

fof(f716,plain,
    ( sK1 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f47,f714])).

fof(f47,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f746,plain,(
    ! [X3] :
      ( sK1 = sK2
      | ~ r1_tarski(sK1,k1_tarski(X3))
      | ~ r2_hidden(X3,sK2) ) ),
    inference(backward_demodulation,[],[f232,f714])).

fof(f232,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,k1_tarski(X3))
      | sK2 = k1_tarski(sK0)
      | ~ r2_hidden(X3,sK2) ) ),
    inference(superposition,[],[f152,f65])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f842,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f732,f838])).

fof(f732,plain,
    ( sK1 = sK2
    | k1_xboole_0 != k4_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f153,f714])).

fof(f153,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f77,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f2479,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f2457,f2439])).

fof(f2439,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f2410,f902])).

fof(f902,plain,(
    k1_xboole_0 != sK2 ),
    inference(trivial_inequality_removal,[],[f898])).

fof(f898,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2 ),
    inference(superposition,[],[f49,f714])).

fof(f49,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f2410,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f2392,f67])).

fof(f2392,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f2158,f1087])).

fof(f2158,plain,(
    ! [X0] :
      ( r2_hidden(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(X0,sK1) ) ),
    inference(resolution,[],[f2121,f53])).

fof(f2121,plain,(
    ! [X2] :
      ( v1_xboole_0(k3_xboole_0(X2,sK1))
      | r2_hidden(sK0,X2) ) ),
    inference(superposition,[],[f2083,f58])).

fof(f2083,plain,(
    ! [X4] :
      ( v1_xboole_0(k3_xboole_0(sK1,X4))
      | r2_hidden(sK0,X4) ) ),
    inference(resolution,[],[f1017,f55])).

fof(f1017,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(sK1,X1))
      | r2_hidden(sK0,X1) ) ),
    inference(resolution,[],[f901,f63])).

fof(f901,plain,(
    ! [X1] :
      ( r1_xboole_0(sK1,X1)
      | r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f64,f714])).

fof(f2457,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f386,f2441])).

fof(f2441,plain,(
    sK2 = k4_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f2426,f51])).

fof(f2426,plain,(
    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f61,f2392])).

fof(f386,plain,(
    ! [X0] :
      ( r1_tarski(k4_xboole_0(sK2,X0),sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f380,f254])).

fof(f380,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK2,X2),k1_tarski(sK0)) ),
    inference(superposition,[],[f372,f84])).

fof(f84,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f80,f66])).

fof(f372,plain,(
    ! [X6,X5] : r1_tarski(k4_xboole_0(sK2,X5),k2_xboole_0(X6,k1_tarski(sK0))) ),
    inference(resolution,[],[f154,f57])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(sK0))) ) ),
    inference(resolution,[],[f78,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(X0,k1_tarski(sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f71,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (10148)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (10147)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (10157)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (10174)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.51  % (10155)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (10166)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (10143)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (10146)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (10145)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (10166)Refutation not found, incomplete strategy% (10166)------------------------------
% 0.21/0.51  % (10166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10166)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10166)Memory used [KB]: 10746
% 0.21/0.51  % (10166)Time elapsed: 0.119 s
% 0.21/0.51  % (10166)------------------------------
% 0.21/0.51  % (10166)------------------------------
% 0.21/0.51  % (10163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (10156)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (10173)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (10158)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (10167)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (10150)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (10144)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (10164)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (10149)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (10170)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (10172)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (10171)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (10159)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (10159)Refutation not found, incomplete strategy% (10159)------------------------------
% 0.21/0.54  % (10159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10159)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10159)Memory used [KB]: 6140
% 0.21/0.54  % (10159)Time elapsed: 0.002 s
% 0.21/0.54  % (10159)------------------------------
% 0.21/0.54  % (10159)------------------------------
% 0.21/0.54  % (10160)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (10168)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (10162)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (10161)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (10161)Refutation not found, incomplete strategy% (10161)------------------------------
% 0.21/0.55  % (10161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10161)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10161)Memory used [KB]: 10618
% 0.21/0.55  % (10161)Time elapsed: 0.149 s
% 0.21/0.55  % (10161)------------------------------
% 0.21/0.55  % (10161)------------------------------
% 0.21/0.55  % (10154)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (10152)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (10165)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (10153)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.81/0.61  % (10167)Refutation found. Thanks to Tanya!
% 1.81/0.61  % SZS status Theorem for theBenchmark
% 1.81/0.61  % SZS output start Proof for theBenchmark
% 1.81/0.61  fof(f2480,plain,(
% 1.81/0.61    $false),
% 1.81/0.61    inference(subsumption_resolution,[],[f2479,f1177])).
% 1.81/0.61  fof(f1177,plain,(
% 1.81/0.61    k1_xboole_0 != sK1),
% 1.81/0.61    inference(superposition,[],[f842,f1173])).
% 1.81/0.61  fof(f1173,plain,(
% 1.81/0.61    sK1 = k4_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(forward_demodulation,[],[f1168,f51])).
% 1.81/0.61  fof(f51,plain,(
% 1.81/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f13])).
% 1.81/0.61  fof(f13,axiom,(
% 1.81/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.81/0.61  fof(f1168,plain,(
% 1.81/0.61    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0)),
% 1.81/0.61    inference(superposition,[],[f61,f1099])).
% 1.81/0.61  fof(f1099,plain,(
% 1.81/0.61    k1_xboole_0 = k3_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(resolution,[],[f1096,f53])).
% 1.81/0.61  fof(f53,plain,(
% 1.81/0.61    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f29])).
% 1.81/0.61  fof(f29,plain,(
% 1.81/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.81/0.61  fof(f1096,plain,(
% 1.81/0.61    v1_xboole_0(k3_xboole_0(sK1,sK2))),
% 1.81/0.61    inference(resolution,[],[f1090,f55])).
% 1.81/0.61  fof(f55,plain,(
% 1.81/0.61    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f42])).
% 1.81/0.61  fof(f42,plain,(
% 1.81/0.61    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 1.81/0.61  fof(f41,plain,(
% 1.81/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.81/0.61    inference(rectify,[],[f39])).
% 1.81/0.61  fof(f39,plain,(
% 1.81/0.61    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.81/0.61    inference(nnf_transformation,[],[f2])).
% 1.81/0.61  fof(f2,axiom,(
% 1.81/0.61    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.81/0.61  fof(f1090,plain,(
% 1.81/0.61    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 1.81/0.61    inference(resolution,[],[f1089,f63])).
% 1.81/0.61  fof(f63,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f44])).
% 1.81/0.61  fof(f44,plain,(
% 1.81/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f43])).
% 1.81/0.61  fof(f43,plain,(
% 1.81/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f30,plain,(
% 1.81/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(ennf_transformation,[],[f27])).
% 1.81/0.61  fof(f27,plain,(
% 1.81/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(rectify,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.81/0.61  fof(f1089,plain,(
% 1.81/0.61    r1_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(forward_demodulation,[],[f1088,f714])).
% 1.81/0.61  fof(f714,plain,(
% 1.81/0.61    sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(subsumption_resolution,[],[f712,f254])).
% 1.81/0.61  fof(f254,plain,(
% 1.81/0.61    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.81/0.61    inference(resolution,[],[f252,f53])).
% 1.81/0.61  fof(f252,plain,(
% 1.81/0.61    v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(resolution,[],[f250,f55])).
% 1.81/0.61  fof(f250,plain,(
% 1.81/0.61    ( ! [X0] : (~r2_hidden(X0,sK1) | sK1 = k1_tarski(sK0)) )),
% 1.81/0.61    inference(forward_demodulation,[],[f249,f83])).
% 1.81/0.61  fof(f83,plain,(
% 1.81/0.61    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.81/0.61    inference(resolution,[],[f80,f67])).
% 1.81/0.61  fof(f67,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f34])).
% 1.81/0.61  fof(f34,plain,(
% 1.81/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f10])).
% 1.81/0.61  fof(f10,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.81/0.61  fof(f80,plain,(
% 1.81/0.61    r1_tarski(sK1,k1_tarski(sK0))),
% 1.81/0.61    inference(superposition,[],[f56,f46])).
% 1.81/0.61  fof(f46,plain,(
% 1.81/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(cnf_transformation,[],[f38])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f37])).
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f28,plain,(
% 1.81/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.81/0.61    inference(ennf_transformation,[],[f26])).
% 1.81/0.61  fof(f26,negated_conjecture,(
% 1.81/0.61    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.81/0.61    inference(negated_conjecture,[],[f25])).
% 1.81/0.61  fof(f25,conjecture,(
% 1.81/0.61    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.81/0.61  fof(f56,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f14])).
% 1.81/0.61  fof(f14,axiom,(
% 1.81/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.81/0.61  fof(f249,plain,(
% 1.81/0.61    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK1,k1_tarski(sK0))) | sK1 = k1_tarski(sK0)) )),
% 1.81/0.61    inference(forward_demodulation,[],[f248,f58])).
% 1.81/0.61  fof(f58,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.81/0.61  fof(f248,plain,(
% 1.81/0.61    ( ! [X0] : (sK1 = k1_tarski(sK0) | ~r2_hidden(X0,k3_xboole_0(k1_tarski(sK0),sK1))) )),
% 1.81/0.61    inference(resolution,[],[f161,f63])).
% 1.81/0.61  fof(f161,plain,(
% 1.81/0.61    r1_xboole_0(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(resolution,[],[f142,f64])).
% 1.81/0.61  fof(f64,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f31])).
% 1.81/0.61  fof(f31,plain,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f22])).
% 1.81/0.61  fof(f22,axiom,(
% 1.81/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.81/0.61  fof(f142,plain,(
% 1.81/0.61    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(superposition,[],[f83,f65])).
% 1.81/0.61  fof(f65,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f32])).
% 1.81/0.61  fof(f32,plain,(
% 1.81/0.61    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f23])).
% 1.81/0.61  fof(f23,axiom,(
% 1.81/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.81/0.61  fof(f712,plain,(
% 1.81/0.61    k1_xboole_0 != sK1 | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(trivial_inequality_removal,[],[f676])).
% 1.81/0.61  fof(f676,plain,(
% 1.81/0.61    sK2 != sK2 | k1_xboole_0 != sK1 | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(superposition,[],[f48,f660])).
% 1.81/0.61  fof(f660,plain,(
% 1.81/0.61    sK2 = k1_tarski(sK0) | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(subsumption_resolution,[],[f650,f252])).
% 1.81/0.61  fof(f650,plain,(
% 1.81/0.61    sK2 = k1_tarski(sK0) | ~v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(resolution,[],[f235,f251])).
% 1.81/0.61  fof(f251,plain,(
% 1.81/0.61    r1_tarski(sK1,sK1) | sK1 = k1_tarski(sK0)),
% 1.81/0.61    inference(resolution,[],[f250,f141])).
% 1.81/0.61  fof(f141,plain,(
% 1.81/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | r1_tarski(X0,X0)) )),
% 1.81/0.61    inference(resolution,[],[f112,f55])).
% 1.81/0.61  fof(f112,plain,(
% 1.81/0.61    ( ! [X0] : (~v1_xboole_0(X0) | r1_tarski(X0,X0)) )),
% 1.81/0.61    inference(superposition,[],[f106,f53])).
% 1.81/0.61  fof(f106,plain,(
% 1.81/0.61    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.81/0.61    inference(superposition,[],[f57,f94])).
% 1.81/0.61  fof(f94,plain,(
% 1.81/0.61    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK1)),
% 1.81/0.61    inference(resolution,[],[f91,f69])).
% 1.81/0.61  fof(f69,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f45])).
% 1.81/0.61  fof(f45,plain,(
% 1.81/0.61    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.81/0.61    inference(nnf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.81/0.61  fof(f91,plain,(
% 1.81/0.61    r1_tarski(k1_xboole_0,sK1)),
% 1.81/0.61    inference(superposition,[],[f57,f82])).
% 1.81/0.61  fof(f82,plain,(
% 1.81/0.61    k1_xboole_0 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.81/0.61    inference(resolution,[],[f80,f69])).
% 1.81/0.61  fof(f57,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f12])).
% 1.81/0.61  fof(f12,axiom,(
% 1.81/0.61    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.81/0.61  fof(f235,plain,(
% 1.81/0.61    ( ! [X0] : (~r1_tarski(sK1,X0) | sK2 = k1_tarski(sK0) | ~v1_xboole_0(X0)) )),
% 1.81/0.61    inference(superposition,[],[f228,f53])).
% 1.81/0.61  fof(f228,plain,(
% 1.81/0.61    ~r1_tarski(sK1,k1_xboole_0) | sK2 = k1_tarski(sK0)),
% 1.81/0.61    inference(superposition,[],[f152,f50])).
% 1.81/0.61  fof(f50,plain,(
% 1.81/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f11])).
% 1.81/0.61  fof(f11,axiom,(
% 1.81/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.81/0.61  fof(f152,plain,(
% 1.81/0.61    ( ! [X0] : (~r1_tarski(sK1,k3_xboole_0(sK2,X0)) | sK2 = k1_tarski(sK0)) )),
% 1.81/0.61    inference(resolution,[],[f77,f72])).
% 1.81/0.61  fof(f72,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f36])).
% 1.81/0.61  fof(f36,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.81/0.61    inference(ennf_transformation,[],[f9])).
% 1.81/0.61  fof(f9,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).
% 1.81/0.61  fof(f77,plain,(
% 1.81/0.61    ~r1_tarski(sK1,sK2) | sK2 = k1_tarski(sK0)),
% 1.81/0.61    inference(superposition,[],[f46,f66])).
% 1.81/0.61  fof(f66,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f33])).
% 1.81/0.61  fof(f33,plain,(
% 1.81/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.81/0.61  fof(f48,plain,(
% 1.81/0.61    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.81/0.61    inference(cnf_transformation,[],[f38])).
% 1.81/0.61  fof(f1088,plain,(
% 1.81/0.61    r1_xboole_0(k1_tarski(sK0),sK2)),
% 1.81/0.61    inference(resolution,[],[f1087,f64])).
% 1.81/0.61  fof(f1087,plain,(
% 1.81/0.61    ~r2_hidden(sK0,sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1085,f720])).
% 1.81/0.61  fof(f720,plain,(
% 1.81/0.61    r1_tarski(sK1,sK1)),
% 1.81/0.61    inference(backward_demodulation,[],[f80,f714])).
% 1.81/0.61  fof(f1085,plain,(
% 1.81/0.61    ~r1_tarski(sK1,sK1) | ~r2_hidden(sK0,sK2)),
% 1.81/0.61    inference(superposition,[],[f847,f714])).
% 1.81/0.61  fof(f847,plain,(
% 1.81/0.61    ( ! [X3] : (~r1_tarski(sK1,k1_tarski(X3)) | ~r2_hidden(X3,sK2)) )),
% 1.81/0.61    inference(subsumption_resolution,[],[f746,f838])).
% 1.81/0.61  fof(f838,plain,(
% 1.81/0.61    sK1 != sK2),
% 1.81/0.61    inference(forward_demodulation,[],[f837,f714])).
% 1.81/0.61  fof(f837,plain,(
% 1.81/0.61    sK2 != k1_tarski(sK0)),
% 1.81/0.61    inference(trivial_inequality_removal,[],[f716])).
% 1.81/0.61  fof(f716,plain,(
% 1.81/0.61    sK1 != sK1 | sK2 != k1_tarski(sK0)),
% 1.81/0.61    inference(backward_demodulation,[],[f47,f714])).
% 1.81/0.61  fof(f47,plain,(
% 1.81/0.61    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.81/0.61    inference(cnf_transformation,[],[f38])).
% 1.81/0.61  fof(f746,plain,(
% 1.81/0.61    ( ! [X3] : (sK1 = sK2 | ~r1_tarski(sK1,k1_tarski(X3)) | ~r2_hidden(X3,sK2)) )),
% 1.81/0.61    inference(backward_demodulation,[],[f232,f714])).
% 1.81/0.61  fof(f232,plain,(
% 1.81/0.61    ( ! [X3] : (~r1_tarski(sK1,k1_tarski(X3)) | sK2 = k1_tarski(sK0) | ~r2_hidden(X3,sK2)) )),
% 1.81/0.61    inference(superposition,[],[f152,f65])).
% 1.81/0.61  fof(f61,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.81/0.61  fof(f842,plain,(
% 1.81/0.61    k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(subsumption_resolution,[],[f732,f838])).
% 1.81/0.61  fof(f732,plain,(
% 1.81/0.61    sK1 = sK2 | k1_xboole_0 != k4_xboole_0(sK1,sK2)),
% 1.81/0.61    inference(backward_demodulation,[],[f153,f714])).
% 1.81/0.61  fof(f153,plain,(
% 1.81/0.61    k1_xboole_0 != k4_xboole_0(sK1,sK2) | sK2 = k1_tarski(sK0)),
% 1.81/0.61    inference(resolution,[],[f77,f68])).
% 1.81/0.61  fof(f68,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f45])).
% 1.81/0.61  fof(f2479,plain,(
% 1.81/0.61    k1_xboole_0 = sK1),
% 1.81/0.61    inference(subsumption_resolution,[],[f2457,f2439])).
% 1.81/0.61  fof(f2439,plain,(
% 1.81/0.61    ~r1_tarski(sK2,sK1)),
% 1.81/0.61    inference(subsumption_resolution,[],[f2410,f902])).
% 1.81/0.61  fof(f902,plain,(
% 1.81/0.61    k1_xboole_0 != sK2),
% 1.81/0.61    inference(trivial_inequality_removal,[],[f898])).
% 1.81/0.61  fof(f898,plain,(
% 1.81/0.61    sK1 != sK1 | k1_xboole_0 != sK2),
% 1.81/0.61    inference(superposition,[],[f49,f714])).
% 1.81/0.61  fof(f49,plain,(
% 1.81/0.61    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.81/0.61    inference(cnf_transformation,[],[f38])).
% 1.81/0.61  fof(f2410,plain,(
% 1.81/0.61    k1_xboole_0 = sK2 | ~r1_tarski(sK2,sK1)),
% 1.81/0.61    inference(superposition,[],[f2392,f67])).
% 1.81/0.61  fof(f2392,plain,(
% 1.81/0.61    k1_xboole_0 = k3_xboole_0(sK2,sK1)),
% 1.81/0.61    inference(resolution,[],[f2158,f1087])).
% 1.81/0.61  fof(f2158,plain,(
% 1.81/0.61    ( ! [X0] : (r2_hidden(sK0,X0) | k1_xboole_0 = k3_xboole_0(X0,sK1)) )),
% 1.81/0.61    inference(resolution,[],[f2121,f53])).
% 1.81/0.61  fof(f2121,plain,(
% 1.81/0.61    ( ! [X2] : (v1_xboole_0(k3_xboole_0(X2,sK1)) | r2_hidden(sK0,X2)) )),
% 1.81/0.61    inference(superposition,[],[f2083,f58])).
% 1.81/0.61  fof(f2083,plain,(
% 1.81/0.61    ( ! [X4] : (v1_xboole_0(k3_xboole_0(sK1,X4)) | r2_hidden(sK0,X4)) )),
% 1.81/0.61    inference(resolution,[],[f1017,f55])).
% 1.81/0.61  fof(f1017,plain,(
% 1.81/0.61    ( ! [X2,X1] : (~r2_hidden(X2,k3_xboole_0(sK1,X1)) | r2_hidden(sK0,X1)) )),
% 1.81/0.61    inference(resolution,[],[f901,f63])).
% 1.81/0.61  fof(f901,plain,(
% 1.81/0.61    ( ! [X1] : (r1_xboole_0(sK1,X1) | r2_hidden(sK0,X1)) )),
% 1.81/0.61    inference(superposition,[],[f64,f714])).
% 1.81/0.61  fof(f2457,plain,(
% 1.81/0.61    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 1.81/0.61    inference(superposition,[],[f386,f2441])).
% 1.81/0.61  fof(f2441,plain,(
% 1.81/0.61    sK2 = k4_xboole_0(sK2,sK1)),
% 1.81/0.61    inference(forward_demodulation,[],[f2426,f51])).
% 1.81/0.61  fof(f2426,plain,(
% 1.81/0.61    k4_xboole_0(sK2,sK1) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.81/0.61    inference(superposition,[],[f61,f2392])).
% 1.81/0.61  fof(f386,plain,(
% 1.81/0.61    ( ! [X0] : (r1_tarski(k4_xboole_0(sK2,X0),sK1) | k1_xboole_0 = sK1) )),
% 1.81/0.61    inference(superposition,[],[f380,f254])).
% 1.81/0.61  fof(f380,plain,(
% 1.81/0.61    ( ! [X2] : (r1_tarski(k4_xboole_0(sK2,X2),k1_tarski(sK0))) )),
% 1.81/0.61    inference(superposition,[],[f372,f84])).
% 1.81/0.61  fof(f84,plain,(
% 1.81/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,k1_tarski(sK0))),
% 1.81/0.61    inference(resolution,[],[f80,f66])).
% 1.81/0.61  fof(f372,plain,(
% 1.81/0.61    ( ! [X6,X5] : (r1_tarski(k4_xboole_0(sK2,X5),k2_xboole_0(X6,k1_tarski(sK0)))) )),
% 1.81/0.61    inference(resolution,[],[f154,f57])).
% 1.81/0.61  fof(f154,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_tarski(X0,sK2) | r1_tarski(X0,k2_xboole_0(X1,k1_tarski(sK0)))) )),
% 1.81/0.61    inference(resolution,[],[f78,f71])).
% 1.81/0.61  fof(f71,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f35])).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f7])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.81/0.61  fof(f78,plain,(
% 1.81/0.61    ( ! [X0] : (r1_tarski(X0,k1_tarski(sK0)) | ~r1_tarski(X0,sK2)) )),
% 1.81/0.61    inference(superposition,[],[f71,f46])).
% 1.81/0.62  % SZS output end Proof for theBenchmark
% 1.81/0.62  % (10167)------------------------------
% 1.81/0.62  % (10167)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (10167)Termination reason: Refutation
% 1.81/0.62  
% 1.81/0.62  % (10167)Memory used [KB]: 2558
% 1.81/0.62  % (10167)Time elapsed: 0.153 s
% 1.81/0.62  % (10167)------------------------------
% 1.81/0.62  % (10167)------------------------------
% 1.81/0.62  % (10142)Success in time 0.259 s
%------------------------------------------------------------------------------
