%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0216+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  37 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   27 (  62 expanded)
%              Number of equality atoms :   26 (  61 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f17])).

fof(f17,plain,(
    sK0 != sK2 ),
    inference(backward_demodulation,[],[f8,f14])).

fof(f14,plain,(
    sK0 = sK1 ),
    inference(equality_resolution,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK0)
      | sK1 = X0 ) ),
    inference(superposition,[],[f10,f7])).

fof(f7,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_tarski(X1,X2)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f8,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f5])).

fof(f23,plain,(
    sK0 = sK2 ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X6] :
      ( k1_tarski(sK0) != k1_tarski(X6)
      | sK2 = X6 ) ),
    inference(superposition,[],[f12,f16])).

fof(f16,plain,(
    k1_tarski(sK0) = k2_tarski(sK0,sK2) ),
    inference(backward_demodulation,[],[f7,f14])).

fof(f12,plain,(
    ! [X2,X3,X1] :
      ( k2_tarski(X2,X1) != k1_tarski(X3)
      | X1 = X3 ) ),
    inference(superposition,[],[f10,f9])).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

%------------------------------------------------------------------------------
