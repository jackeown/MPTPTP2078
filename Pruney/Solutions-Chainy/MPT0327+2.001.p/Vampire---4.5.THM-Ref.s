%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 (2307 expanded)
%              Number of leaves         :   12 ( 692 expanded)
%              Depth                    :   30
%              Number of atoms          :  116 (4261 expanded)
%              Number of equality atoms :   79 (1953 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f538])).

fof(f538,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f527,f394])).

fof(f394,plain,(
    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f51,f380])).

fof(f380,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f264,f115])).

fof(f115,plain,(
    sK1 = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f109,f95])).

fof(f95,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f70,f71])).

fof(f71,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f67,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f46,f36,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f67,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) ),
    inference(resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f45,f36])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r1_tarski(k2_tarski(sK0,X0),sK1) ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f70,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) ),
    inference(forward_demodulation,[],[f69,f56])).

fof(f69,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))) ),
    inference(resolution,[],[f64,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X1 ) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f109,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f97,f82])).

fof(f82,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f51,f67])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(sK1,X0) ),
    inference(superposition,[],[f48,f95])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f264,plain,(
    ! [X12] : k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),X12)) = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),X12)) ),
    inference(superposition,[],[f51,f89])).

fof(f89,plain,(
    ! [X2] : k4_xboole_0(k2_tarski(sK0,sK0),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),X2))) ),
    inference(superposition,[],[f54,f71])).

fof(f54,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f35,f36,f36])).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f527,plain,(
    sK1 != k5_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f511,f397])).

fof(f397,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f394,f171])).

fof(f171,plain,(
    ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f157,f51])).

fof(f157,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f147,f51])).

fof(f147,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f146,f48])).

fof(f146,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK1),X0)) ),
    inference(superposition,[],[f48,f142])).

fof(f142,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f140,f95])).

fof(f140,plain,(
    k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f97,f136])).

fof(f136,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f114,f48])).

fof(f114,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f108,f94])).

fof(f94,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f51,f71])).

fof(f108,plain,(
    k5_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),sK1) ),
    inference(superposition,[],[f97,f101])).

fof(f101,plain,(
    sK1 = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f96,f90])).

fof(f90,plain,(
    k4_xboole_0(sK1,k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f51,f71])).

fof(f96,plain,(
    sK1 = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f95,f48])).

fof(f511,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f465,f496])).

fof(f496,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f487,f387])).

fof(f387,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f89,f380])).

fof(f487,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f77,f423])).

fof(f423,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f422,f71])).

fof(f422,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f411,f56])).

fof(f411,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f77,f397])).

fof(f77,plain,(
    ! [X2] : k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,X2))) = k4_xboole_0(k2_tarski(sK0,sK0),X2) ),
    inference(superposition,[],[f54,f67])).

fof(f465,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f374,f387])).

fof(f374,plain,(
    sK1 != k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f344,f264])).

fof(f344,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f338,f78])).

fof(f78,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f51,f67])).

fof(f338,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f119,f102])).

fof(f102,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),X0) ),
    inference(superposition,[],[f48,f90])).

fof(f119,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))) ),
    inference(backward_demodulation,[],[f60,f77])).

fof(f60,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(forward_demodulation,[],[f52,f56])).

fof(f52,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f32,f50,f38,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:01:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (13306)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.50  % (13286)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (13298)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.51  % (13290)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (13300)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (13283)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (13302)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (13282)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (13306)Refutation not found, incomplete strategy% (13306)------------------------------
% 0.20/0.52  % (13306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13298)Refutation not found, incomplete strategy% (13298)------------------------------
% 0.20/0.52  % (13298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13298)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13298)Memory used [KB]: 10618
% 0.20/0.52  % (13298)Time elapsed: 0.112 s
% 0.20/0.52  % (13298)------------------------------
% 0.20/0.52  % (13298)------------------------------
% 0.20/0.52  % (13292)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (13306)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13306)Memory used [KB]: 10618
% 0.20/0.52  % (13306)Time elapsed: 0.112 s
% 0.20/0.52  % (13306)------------------------------
% 0.20/0.52  % (13306)------------------------------
% 0.20/0.52  % (13292)Refutation not found, incomplete strategy% (13292)------------------------------
% 0.20/0.52  % (13292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13292)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13292)Memory used [KB]: 10746
% 0.20/0.52  % (13292)Time elapsed: 0.114 s
% 0.20/0.52  % (13292)------------------------------
% 0.20/0.52  % (13292)------------------------------
% 0.20/0.52  % (13294)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (13285)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (13291)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.53  % (13288)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (13311)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (13284)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (13293)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (13300)Refutation not found, incomplete strategy% (13300)------------------------------
% 0.20/0.53  % (13300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13300)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13300)Memory used [KB]: 1663
% 0.20/0.53  % (13300)Time elapsed: 0.124 s
% 0.20/0.53  % (13300)------------------------------
% 0.20/0.53  % (13300)------------------------------
% 0.20/0.53  % (13311)Refutation not found, incomplete strategy% (13311)------------------------------
% 0.20/0.53  % (13311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13311)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13311)Memory used [KB]: 1663
% 0.20/0.53  % (13311)Time elapsed: 0.125 s
% 0.20/0.53  % (13311)------------------------------
% 0.20/0.53  % (13311)------------------------------
% 0.20/0.53  % (13287)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (13299)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (13289)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.53  % (13283)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f540,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f538])).
% 0.20/0.53  fof(f538,plain,(
% 0.20/0.53    sK1 != sK1),
% 0.20/0.53    inference(superposition,[],[f527,f394])).
% 0.20/0.53  fof(f394,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(superposition,[],[f51,f380])).
% 0.20/0.53  fof(f380,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f264,f115])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(forward_demodulation,[],[f109,f95])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k2_tarski(sK0,sK0))),
% 0.20/0.53    inference(forward_demodulation,[],[f70,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f67,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f46,f36,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1))),
% 0.20/0.53    inference(resolution,[],[f64,f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f45,f36])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    r1_tarski(k2_tarski(sK0,sK0),sK1)),
% 0.20/0.53    inference(resolution,[],[f61,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    r2_hidden(sK0,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.53    inference(negated_conjecture,[],[f20])).
% 0.20/0.53  fof(f20,conjecture,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | r1_tarski(k2_tarski(sK0,X0),sK1)) )),
% 0.20/0.53    inference(resolution,[],[f31,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(flattening,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.53    inference(nnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))))),
% 0.20/0.53    inference(forward_demodulation,[],[f69,f56])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)))),
% 0.20/0.53    inference(resolution,[],[f64,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X1) )),
% 0.20/0.53    inference(definition_unfolding,[],[f33,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f34,f36])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f97,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f51,f67])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(sK1,X0)) )),
% 0.20/0.53    inference(superposition,[],[f48,f95])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.53  fof(f264,plain,(
% 0.20/0.53    ( ! [X12] : (k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),X12)) = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),X12))) )),
% 0.20/0.53    inference(superposition,[],[f51,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X2] : (k4_xboole_0(k2_tarski(sK0,sK0),X2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),X2)))) )),
% 0.20/0.53    inference(superposition,[],[f54,f71])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.53    inference(definition_unfolding,[],[f35,f36,f36])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.53    inference(definition_unfolding,[],[f37,f36])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.53  fof(f527,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f511,f397])).
% 0.20/0.53  fof(f397,plain,(
% 0.20/0.53    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(superposition,[],[f394,f171])).
% 0.20/0.53  fof(f171,plain,(
% 0.20/0.53    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 0.20/0.53    inference(superposition,[],[f157,f51])).
% 0.20/0.53  fof(f157,plain,(
% 0.20/0.53    ( ! [X0] : (k4_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,X0)))) )),
% 0.20/0.53    inference(superposition,[],[f147,f51])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) )),
% 0.20/0.53    inference(forward_demodulation,[],[f146,f48])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK1),X0))) )),
% 0.20/0.53    inference(superposition,[],[f48,f142])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f140,f95])).
% 0.20/0.53  fof(f140,plain,(
% 0.20/0.53    k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(superposition,[],[f97,f136])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(superposition,[],[f114,f48])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),sK1)),
% 0.20/0.53    inference(forward_demodulation,[],[f108,f94])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f51,f71])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    k5_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) = k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),sK1),sK1)),
% 0.20/0.53    inference(superposition,[],[f97,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f96,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    k4_xboole_0(sK1,k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k2_tarski(sK0,sK0))),
% 0.20/0.53    inference(superposition,[],[f51,f71])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    sK1 = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(superposition,[],[f95,f48])).
% 0.20/0.53  fof(f511,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)),k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(backward_demodulation,[],[f465,f496])).
% 0.20/0.53  fof(f496,plain,(
% 0.20/0.53    k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k4_xboole_0(sK1,sK1)),
% 0.20/0.53    inference(forward_demodulation,[],[f487,f387])).
% 0.20/0.53  fof(f387,plain,(
% 0.20/0.53    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) = k4_xboole_0(sK1,sK1)),
% 0.20/0.53    inference(superposition,[],[f89,f380])).
% 0.20/0.53  fof(f487,plain,(
% 0.20/0.53    k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.20/0.53    inference(superposition,[],[f77,f423])).
% 0.20/0.53  fof(f423,plain,(
% 0.20/0.53    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f422,f71])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(forward_demodulation,[],[f411,f56])).
% 0.20/0.53  fof(f411,plain,(
% 0.20/0.53    k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(superposition,[],[f77,f397])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X2] : (k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,X2))) = k4_xboole_0(k2_tarski(sK0,sK0),X2)) )),
% 0.20/0.53    inference(superposition,[],[f54,f67])).
% 0.20/0.53  fof(f465,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(sK1,sK1))),
% 0.20/0.53    inference(backward_demodulation,[],[f374,f387])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k4_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f344,f264])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(forward_demodulation,[],[f338,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.20/0.53    inference(superposition,[],[f51,f67])).
% 0.20/0.53  fof(f338,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f119,f102])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),X0)) )),
% 0.20/0.53    inference(superposition,[],[f48,f90])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)))),
% 0.20/0.53    inference(backward_demodulation,[],[f60,f77])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 0.20/0.53    inference(forward_demodulation,[],[f52,f56])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))))),
% 0.20/0.53    inference(definition_unfolding,[],[f32,f50,f38,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,axiom,(
% 0.20/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f26])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (13283)------------------------------
% 0.20/0.53  % (13283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13283)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (13283)Memory used [KB]: 2046
% 0.20/0.53  % (13283)Time elapsed: 0.130 s
% 0.20/0.53  % (13283)------------------------------
% 0.20/0.53  % (13283)------------------------------
% 0.20/0.54  % (13281)Success in time 0.183 s
%------------------------------------------------------------------------------
