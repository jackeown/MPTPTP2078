%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 (1954 expanded)
%              Number of leaves         :   14 ( 652 expanded)
%              Depth                    :   33
%              Number of atoms          :  107 (2002 expanded)
%              Number of equality atoms :   83 (1954 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1265,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1264,f707])).

fof(f707,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7 ),
    inference(superposition,[],[f618,f563])).

fof(f563,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f42,f538])).

fof(f538,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f48,f506])).

fof(f506,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f59,f503])).

fof(f503,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(forward_demodulation,[],[f502,f436])).

fof(f436,plain,(
    ! [X1] : k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = X1 ),
    inference(forward_demodulation,[],[f433,f23])).

fof(f23,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f433,plain,(
    ! [X1] : k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X1 ),
    inference(superposition,[],[f40,f416])).

fof(f416,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f415,f151])).

fof(f151,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f64,f72])).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f42,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f61,f23])).

fof(f61,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f42,f48])).

fof(f415,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f359,f59])).

fof(f359,plain,(
    ! [X0] : k3_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f37,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f502,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f501,f23])).

fof(f501,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f500,f42])).

fof(f500,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f497,f23])).

fof(f497,plain,(
    ! [X0] : k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0)))) ),
    inference(superposition,[],[f37,f450])).

fof(f450,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f449,f59])).

fof(f449,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f448,f64])).

fof(f448,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f447,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f447,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(X0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f446,f23])).

fof(f446,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f445,f23])).

fof(f445,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0)))) ),
    inference(forward_demodulation,[],[f443,f31])).

fof(f443,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,X0))) ),
    inference(superposition,[],[f37,f436])).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f42,f48])).

fof(f48,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f42,f23])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f31,f23])).

fof(f618,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f601,f506])).

fof(f601,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f563,f44])).

fof(f44,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f31,f23])).

fof(f1264,plain,(
    sK2 != k5_xboole_0(k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1263,f506])).

fof(f1263,plain,(
    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k1_xboole_0)),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1077,f1170])).

fof(f1170,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1156,f23])).

fof(f1156,plain,(
    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f563,f1147])).

fof(f1147,plain,(
    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(resolution,[],[f936,f19])).

fof(f19,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f936,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(X1,X1,X1,X1,sK1))) ) ),
    inference(resolution,[],[f41,f20])).

fof(f20,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1))) = X2 ) ),
    inference(definition_unfolding,[],[f32,f27,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f1077,plain,(
    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1076,f886])).

fof(f886,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[],[f603,f37])).

fof(f603,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k5_xboole_0(X6,X7),k5_xboole_0(X6,k5_xboole_0(X7,X8))) = X8 ),
    inference(superposition,[],[f563,f31])).

fof(f1076,plain,(
    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f1075,f644])).

fof(f644,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = X2 ),
    inference(superposition,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f34,f34])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1075,plain,(
    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))))) ),
    inference(forward_demodulation,[],[f38,f886])).

fof(f38,plain,(
    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_enumset1(sK0,sK0,sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f27,f34,f36,f36])).

fof(f21,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 12:35:46 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.44  % (27033)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (27034)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.46  % (27026)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (27027)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (27037)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (27031)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (27033)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1265,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f1264,f707])).
% 0.21/0.48  fof(f707,plain,(
% 0.21/0.48    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,X8),X8) = X7) )),
% 0.21/0.48    inference(superposition,[],[f618,f563])).
% 0.21/0.48  fof(f563,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.21/0.48    inference(backward_demodulation,[],[f42,f538])).
% 0.21/0.48  fof(f538,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.48    inference(backward_demodulation,[],[f48,f506])).
% 0.21/0.48  fof(f506,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(backward_demodulation,[],[f59,f503])).
% 0.21/0.48  fof(f503,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f502,f436])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k1_xboole_0)) = X1) )),
% 0.21/0.48    inference(forward_demodulation,[],[f433,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.48  fof(f433,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = X1) )),
% 0.21/0.48    inference(superposition,[],[f40,f416])).
% 0.21/0.48  fof(f416,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f415,f151])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(superposition,[],[f64,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.48    inference(superposition,[],[f42,f64])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f61,f23])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0))) )),
% 0.21/0.48    inference(superposition,[],[f42,f48])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f359,f59])).
% 0.21/0.48  fof(f359,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X0),k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)))) )),
% 0.21/0.48    inference(superposition,[],[f37,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f29,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f25,f34])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.48  fof(f502,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f501,f23])).
% 0.21/0.48  fof(f501,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f500,f42])).
% 0.21/0.48  fof(f500,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f497,f23])).
% 0.21/0.48  fof(f497,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X0,k1_xboole_0)),k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,k1_xboole_0))))) )),
% 0.21/0.48    inference(superposition,[],[f37,f450])).
% 0.21/0.48  fof(f450,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f449,f59])).
% 0.21/0.48  fof(f449,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f448,f64])).
% 0.21/0.48  fof(f448,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X0)),k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f447,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.48  fof(f447,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f446,f23])).
% 0.21/0.48  fof(f446,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f445,f23])).
% 0.21/0.48  fof(f445,plain,(
% 0.21/0.48    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X0))))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f443,f31])).
% 0.21/0.49  fof(f443,plain,(
% 0.21/0.49    ( ! [X0] : (k3_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0),k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k5_xboole_0(X0,X0)))) )),
% 0.21/0.49    inference(superposition,[],[f37,f436])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.49    inference(superposition,[],[f42,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.49    inference(superposition,[],[f42,f23])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.21/0.49    inference(superposition,[],[f31,f23])).
% 0.21/0.49  fof(f618,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 0.21/0.49    inference(forward_demodulation,[],[f601,f506])).
% 0.21/0.49  fof(f601,plain,(
% 0.21/0.49    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 0.21/0.49    inference(superposition,[],[f563,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 0.21/0.49    inference(superposition,[],[f31,f23])).
% 0.21/0.49  fof(f1264,plain,(
% 0.21/0.49    sK2 != k5_xboole_0(k5_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f1263,f506])).
% 0.21/0.49  fof(f1263,plain,(
% 0.21/0.49    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k1_xboole_0)),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f1077,f1170])).
% 0.21/0.49  fof(f1170,plain,(
% 0.21/0.49    k1_xboole_0 = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f1156,f23])).
% 0.21/0.49  fof(f1156,plain,(
% 0.21/0.49    k5_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.49    inference(superposition,[],[f563,f1147])).
% 0.21/0.49  fof(f1147,plain,(
% 0.21/0.49    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.21/0.49    inference(resolution,[],[f936,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ~r2_hidden(sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.49    inference(negated_conjecture,[],[f13])).
% 0.21/0.49  fof(f13,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 0.21/0.49  fof(f936,plain,(
% 0.21/0.49    ( ! [X1] : (r2_hidden(X1,sK2) | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,k3_enumset1(X1,X1,X1,X1,sK1)))) )),
% 0.21/0.49    inference(resolution,[],[f41,f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ~r2_hidden(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k5_xboole_0(X2,k3_xboole_0(X2,k3_enumset1(X0,X0,X0,X0,X1))) = X2) )),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f27,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f26,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f30,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.21/0.49  fof(f1077,plain,(
% 0.21/0.49    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(sK2,k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f1076,f886])).
% 0.21/0.49  fof(f886,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(superposition,[],[f603,f37])).
% 0.21/0.49  fof(f603,plain,(
% 0.21/0.49    ( ! [X6,X8,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),k5_xboole_0(X6,k5_xboole_0(X7,X8))) = X8) )),
% 0.21/0.49    inference(superposition,[],[f563,f31])).
% 0.21/0.49  fof(f1076,plain,(
% 0.21/0.49    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_enumset1(sK0,sK0,sK0,sK0,sK1))),
% 0.21/0.49    inference(forward_demodulation,[],[f1075,f644])).
% 0.21/0.49  fof(f644,plain,(
% 0.21/0.49    ( ! [X2,X3] : (k3_xboole_0(X2,k5_xboole_0(X3,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) = X2) )),
% 0.21/0.49    inference(superposition,[],[f40,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 0.21/0.49    inference(definition_unfolding,[],[f24,f34,f34])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.49  fof(f1075,plain,(
% 0.21/0.49    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2)))))),
% 0.21/0.49    inference(forward_demodulation,[],[f38,f886])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    sK2 != k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),sK2))),k3_enumset1(sK0,sK0,sK0,sK0,sK1)))),
% 0.21/0.49    inference(definition_unfolding,[],[f21,f27,f34,f36,f36])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (27033)------------------------------
% 0.21/0.49  % (27033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27033)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (27033)Memory used [KB]: 2430
% 0.21/0.49  % (27033)Time elapsed: 0.086 s
% 0.21/0.49  % (27033)------------------------------
% 0.21/0.49  % (27033)------------------------------
% 0.21/0.49  % (27024)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (27015)Success in time 0.128 s
%------------------------------------------------------------------------------
