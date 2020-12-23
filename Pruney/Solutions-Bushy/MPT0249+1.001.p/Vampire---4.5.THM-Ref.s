%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0249+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  50 expanded)
%              Number of leaves         :    2 (  10 expanded)
%              Depth                    :   11
%              Number of atoms          :   54 ( 166 expanded)
%              Number of equality atoms :   53 ( 165 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f35])).

fof(f35,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f34,f28])).

fof(f28,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2] :
      ( k1_tarski(sK0) != k1_tarski(X2)
      | sK1 = k1_tarski(X2) ) ),
    inference(subsumption_resolution,[],[f20,f8])).

fof(f8,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f20,plain,(
    ! [X2] :
      ( k1_tarski(sK0) != k1_tarski(X2)
      | k1_xboole_0 = sK1
      | sK1 = k1_tarski(X2) ) ),
    inference(superposition,[],[f12,f6])).

fof(f6,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f34,plain,(
    ! [X5] : sK1 != k1_tarski(X5) ),
    inference(subsumption_resolution,[],[f33,f7])).

fof(f7,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X5] :
      ( sK1 != k1_tarski(X5)
      | sK1 = sK2 ) ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,(
    ! [X5] :
      ( sK1 != k1_tarski(X5)
      | sK2 = k1_tarski(X5) ) ),
    inference(backward_demodulation,[],[f27,f28])).

fof(f27,plain,(
    ! [X5] :
      ( k1_tarski(sK0) != k1_tarski(X5)
      | sK2 = k1_tarski(X5) ) ),
    inference(subsumption_resolution,[],[f23,f9])).

fof(f9,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X5] :
      ( k1_tarski(sK0) != k1_tarski(X5)
      | sK2 = k1_tarski(X5)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f15,f6])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f5])).

%------------------------------------------------------------------------------
