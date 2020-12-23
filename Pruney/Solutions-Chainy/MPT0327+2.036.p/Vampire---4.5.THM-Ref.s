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
% DateTime   : Thu Dec  3 12:42:53 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 785 expanded)
%              Number of leaves         :   14 ( 245 expanded)
%              Depth                    :   24
%              Number of atoms          :  115 (1190 expanded)
%              Number of equality atoms :   79 ( 709 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(subsumption_resolution,[],[f269,f268])).

fof(f268,plain,(
    sK1 = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(forward_demodulation,[],[f253,f50])).

fof(f50,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f253,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(backward_demodulation,[],[f126,f250])).

fof(f250,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(subsumption_resolution,[],[f235,f67])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f235,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
      | ~ r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f217,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f217,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f200,f57])).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f200,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f183,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f46,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f183,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f172,f59])).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f49,f46])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f172,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f169,f59])).

fof(f169,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(forward_demodulation,[],[f167,f105])).

fof(f105,plain,(
    ! [X0] : k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f48,f96])).

fof(f96,plain,(
    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f90,f57])).

fof(f90,plain,(
    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0)) ),
    inference(superposition,[],[f59,f84])).

fof(f84,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(resolution,[],[f69,f56])).

fof(f69,plain,(
    r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    inference(resolution,[],[f37,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f37,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f167,plain,(
    ! [X0] : k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f105,f164])).

fof(f164,plain,(
    ! [X1] : k5_xboole_0(k2_tarski(sK0,sK0),X1) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k1_xboole_0,X1)) ),
    inference(backward_demodulation,[],[f139,f163])).

fof(f163,plain,(
    ! [X0] : k5_xboole_0(k2_tarski(sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK0,sK0),X0)) ),
    inference(superposition,[],[f48,f143])).

fof(f143,plain,(
    k2_tarski(sK0,sK0) = k5_xboole_0(k1_xboole_0,k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f140,f50])).

fof(f140,plain,(
    k5_xboole_0(k1_xboole_0,k2_tarski(sK0,sK0)) = k5_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f105,f96])).

fof(f139,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK0,sK0),X1)) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f105,f105])).

fof(f126,plain,(
    k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(forward_demodulation,[],[f125,f118])).

fof(f118,plain,(
    k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(backward_demodulation,[],[f103,f111])).

fof(f111,plain,(
    k4_xboole_0(sK1,k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f59,f102])).

fof(f102,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(forward_demodulation,[],[f92,f57])).

fof(f92,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))) ),
    inference(superposition,[],[f64,f84])).

fof(f103,plain,(
    k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    inference(backward_demodulation,[],[f101,f102])).

fof(f101,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f100,f59])).

fof(f100,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1)))) ),
    inference(forward_demodulation,[],[f99,f64])).

fof(f99,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))) ),
    inference(forward_demodulation,[],[f91,f48])).

fof(f91,plain,(
    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))) ),
    inference(superposition,[],[f61,f84])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f40,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f125,plain,(
    k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(forward_demodulation,[],[f124,f64])).

fof(f124,plain,(
    k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) ),
    inference(forward_demodulation,[],[f123,f102])).

fof(f123,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) ),
    inference(forward_demodulation,[],[f122,f59])).

fof(f122,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))) ),
    inference(forward_demodulation,[],[f121,f64])).

fof(f121,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),sK1)))) ),
    inference(forward_demodulation,[],[f115,f48])).

fof(f115,plain,(
    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),sK1),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),sK1))) ),
    inference(superposition,[],[f61,f102])).

fof(f269,plain,(
    sK1 != k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(forward_demodulation,[],[f254,f50])).

fof(f254,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(backward_demodulation,[],[f120,f250])).

fof(f120,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(backward_demodulation,[],[f68,f118])).

fof(f68,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0))))) ),
    inference(forward_demodulation,[],[f60,f64])).

fof(f60,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f38,f58,f43,f43])).

fof(f38,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.36/0.56  % (11003)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.36/0.56  % (11018)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.57  % (11003)Refutation not found, incomplete strategy% (11003)------------------------------
% 1.36/0.57  % (11003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (11003)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.57  
% 1.36/0.57  % (11003)Memory used [KB]: 10618
% 1.36/0.57  % (11003)Time elapsed: 0.131 s
% 1.36/0.57  % (11003)------------------------------
% 1.36/0.57  % (11003)------------------------------
% 1.36/0.57  % (11010)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.36/0.57  % (10995)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.66/0.57  % (11002)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.66/0.59  % (10995)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.59  % SZS output start Proof for theBenchmark
% 1.66/0.59  fof(f270,plain,(
% 1.66/0.59    $false),
% 1.66/0.59    inference(subsumption_resolution,[],[f269,f268])).
% 1.66/0.59  fof(f268,plain,(
% 1.66/0.59    sK1 = k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(forward_demodulation,[],[f253,f50])).
% 1.66/0.59  fof(f50,plain,(
% 1.66/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f11])).
% 1.66/0.59  fof(f11,axiom,(
% 1.66/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.66/0.59  fof(f253,plain,(
% 1.66/0.59    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(backward_demodulation,[],[f126,f250])).
% 1.66/0.59  fof(f250,plain,(
% 1.66/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.66/0.59    inference(subsumption_resolution,[],[f235,f67])).
% 1.66/0.59  fof(f67,plain,(
% 1.66/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.59    inference(equality_resolution,[],[f51])).
% 1.66/0.59  fof(f51,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.66/0.59    inference(cnf_transformation,[],[f35])).
% 1.66/0.59  fof(f35,plain,(
% 1.66/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.59    inference(flattening,[],[f34])).
% 1.66/0.59  fof(f34,plain,(
% 1.66/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.59    inference(nnf_transformation,[],[f4])).
% 1.66/0.59  fof(f4,axiom,(
% 1.66/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.59  fof(f235,plain,(
% 1.66/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) | ~r1_tarski(X1,X1)) )),
% 1.66/0.59    inference(superposition,[],[f217,f56])).
% 1.66/0.59  fof(f56,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f36])).
% 1.66/0.59  fof(f36,plain,(
% 1.66/0.59    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.66/0.59    inference(nnf_transformation,[],[f5])).
% 1.66/0.59  fof(f5,axiom,(
% 1.66/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.66/0.59  fof(f217,plain,(
% 1.66/0.59    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,X2)) )),
% 1.66/0.59    inference(forward_demodulation,[],[f200,f57])).
% 1.66/0.59  fof(f57,plain,(
% 1.66/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.66/0.59    inference(cnf_transformation,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.66/0.59  fof(f200,plain,(
% 1.66/0.59    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k4_xboole_0(X2,k4_xboole_0(X2,k1_xboole_0))) )),
% 1.66/0.59    inference(superposition,[],[f183,f64])).
% 1.66/0.59  fof(f64,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f47,f46,f46])).
% 1.66/0.59  fof(f46,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f10])).
% 1.66/0.59  fof(f10,axiom,(
% 1.66/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f1])).
% 1.66/0.59  fof(f1,axiom,(
% 1.66/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.66/0.59  fof(f183,plain,(
% 1.66/0.59    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.66/0.59    inference(superposition,[],[f172,f59])).
% 1.66/0.59  fof(f59,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f49,f46])).
% 1.66/0.59  fof(f49,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f6])).
% 1.66/0.59  fof(f6,axiom,(
% 1.66/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.66/0.59  fof(f172,plain,(
% 1.66/0.59    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.66/0.59    inference(superposition,[],[f169,f59])).
% 1.66/0.59  fof(f169,plain,(
% 1.66/0.59    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.66/0.59    inference(forward_demodulation,[],[f167,f105])).
% 1.66/0.59  fof(f105,plain,(
% 1.66/0.59    ( ! [X0] : (k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.66/0.59    inference(superposition,[],[f48,f96])).
% 1.66/0.59  fof(f96,plain,(
% 1.66/0.59    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.66/0.59    inference(forward_demodulation,[],[f90,f57])).
% 1.66/0.59  fof(f90,plain,(
% 1.66/0.59    k1_xboole_0 = k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0))),
% 1.66/0.59    inference(superposition,[],[f59,f84])).
% 1.66/0.59  fof(f84,plain,(
% 1.66/0.59    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 1.66/0.59    inference(resolution,[],[f69,f56])).
% 1.66/0.59  fof(f69,plain,(
% 1.66/0.59    r1_tarski(k2_tarski(sK0,sK0),sK1)),
% 1.66/0.59    inference(resolution,[],[f37,f62])).
% 1.66/0.59  fof(f62,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.66/0.59    inference(definition_unfolding,[],[f42,f43])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f16])).
% 1.66/0.59  fof(f16,axiom,(
% 1.66/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f30])).
% 1.66/0.59  fof(f30,plain,(
% 1.66/0.59    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.66/0.59    inference(nnf_transformation,[],[f20])).
% 1.66/0.59  fof(f20,axiom,(
% 1.66/0.59    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    r2_hidden(sK0,sK1)),
% 1.66/0.59    inference(cnf_transformation,[],[f29])).
% 1.66/0.59  fof(f29,plain,(
% 1.66/0.59    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 1.66/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f28])).
% 1.66/0.59  fof(f28,plain,(
% 1.66/0.59    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 1.66/0.59    introduced(choice_axiom,[])).
% 1.66/0.59  fof(f25,plain,(
% 1.66/0.59    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 1.66/0.59    inference(ennf_transformation,[],[f24])).
% 1.66/0.59  fof(f24,negated_conjecture,(
% 1.66/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.66/0.59    inference(negated_conjecture,[],[f23])).
% 1.66/0.59  fof(f23,conjecture,(
% 1.66/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,axiom,(
% 1.66/0.59    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.66/0.59  fof(f167,plain,(
% 1.66/0.59    ( ! [X0] : (k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK0),X0)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) )),
% 1.66/0.59    inference(superposition,[],[f105,f164])).
% 1.66/0.59  fof(f164,plain,(
% 1.66/0.59    ( ! [X1] : (k5_xboole_0(k2_tarski(sK0,sK0),X1) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k1_xboole_0,X1))) )),
% 1.66/0.59    inference(backward_demodulation,[],[f139,f163])).
% 1.66/0.59  fof(f163,plain,(
% 1.66/0.59    ( ! [X0] : (k5_xboole_0(k2_tarski(sK0,sK0),X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK0,sK0),X0))) )),
% 1.66/0.59    inference(superposition,[],[f48,f143])).
% 1.66/0.59  fof(f143,plain,(
% 1.66/0.59    k2_tarski(sK0,sK0) = k5_xboole_0(k1_xboole_0,k2_tarski(sK0,sK0))),
% 1.66/0.59    inference(forward_demodulation,[],[f140,f50])).
% 1.66/0.59  fof(f140,plain,(
% 1.66/0.59    k5_xboole_0(k1_xboole_0,k2_tarski(sK0,sK0)) = k5_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0)),
% 1.66/0.59    inference(superposition,[],[f105,f96])).
% 1.66/0.59  fof(f139,plain,(
% 1.66/0.59    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_tarski(sK0,sK0),X1)) = k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k1_xboole_0,X1))) )),
% 1.66/0.59    inference(superposition,[],[f105,f105])).
% 1.66/0.59  fof(f126,plain,(
% 1.66/0.59    k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(forward_demodulation,[],[f125,f118])).
% 1.66/0.59  fof(f118,plain,(
% 1.66/0.59    k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1))),
% 1.66/0.59    inference(backward_demodulation,[],[f103,f111])).
% 1.66/0.59  fof(f111,plain,(
% 1.66/0.59    k4_xboole_0(sK1,k2_tarski(sK0,sK0)) = k5_xboole_0(sK1,k2_tarski(sK0,sK0))),
% 1.66/0.59    inference(superposition,[],[f59,f102])).
% 1.66/0.59  fof(f102,plain,(
% 1.66/0.59    k2_tarski(sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 1.66/0.59    inference(forward_demodulation,[],[f92,f57])).
% 1.66/0.59  fof(f92,plain,(
% 1.66/0.59    k4_xboole_0(k2_tarski(sK0,sK0),k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))),
% 1.66/0.59    inference(superposition,[],[f64,f84])).
% 1.66/0.59  fof(f103,plain,(
% 1.66/0.59    k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 1.66/0.59    inference(backward_demodulation,[],[f101,f102])).
% 1.66/0.59  fof(f101,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1))),
% 1.66/0.59    inference(forward_demodulation,[],[f100,f59])).
% 1.66/0.59  fof(f100,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK1))))),
% 1.66/0.59    inference(forward_demodulation,[],[f99,f64])).
% 1.66/0.59  fof(f99,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0))))),
% 1.66/0.59    inference(forward_demodulation,[],[f91,f48])).
% 1.66/0.59  fof(f91,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(sK1,k4_xboole_0(sK1,k1_xboole_0)))),
% 1.66/0.59    inference(superposition,[],[f61,f84])).
% 1.66/0.59  fof(f61,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f40,f58,f58])).
% 1.66/0.59  fof(f58,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.66/0.59    inference(definition_unfolding,[],[f39,f46])).
% 1.66/0.59  fof(f39,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  fof(f15,axiom,(
% 1.66/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.66/0.59  fof(f40,plain,(
% 1.66/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f8])).
% 1.66/0.59  fof(f8,axiom,(
% 1.66/0.59    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.66/0.59  fof(f125,plain,(
% 1.66/0.59    k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(forward_demodulation,[],[f124,f64])).
% 1.66/0.59  fof(f124,plain,(
% 1.66/0.59    k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))))),
% 1.66/0.59    inference(forward_demodulation,[],[f123,f102])).
% 1.66/0.59  fof(f123,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))))),
% 1.66/0.59    inference(forward_demodulation,[],[f122,f59])).
% 1.66/0.59  fof(f122,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK0,sK0))))))),
% 1.66/0.59    inference(forward_demodulation,[],[f121,f64])).
% 1.66/0.59  fof(f121,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),sK1))))),
% 1.66/0.59    inference(forward_demodulation,[],[f115,f48])).
% 1.66/0.59  fof(f115,plain,(
% 1.66/0.59    k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),sK1),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),sK1)))),
% 1.66/0.59    inference(superposition,[],[f61,f102])).
% 1.66/0.59  fof(f269,plain,(
% 1.66/0.59    sK1 != k5_xboole_0(sK1,k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(forward_demodulation,[],[f254,f50])).
% 1.66/0.59  fof(f254,plain,(
% 1.66/0.59    sK1 != k5_xboole_0(k5_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(backward_demodulation,[],[f120,f250])).
% 1.66/0.59  fof(f120,plain,(
% 1.66/0.59    sK1 != k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(k1_xboole_0,sK1)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(backward_demodulation,[],[f68,f118])).
% 1.66/0.59  fof(f68,plain,(
% 1.66/0.59    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(sK1,k2_tarski(sK0,sK0)))))),
% 1.66/0.59    inference(forward_demodulation,[],[f60,f64])).
% 1.66/0.59  fof(f60,plain,(
% 1.66/0.59    sK1 != k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k4_xboole_0(k4_xboole_0(sK1,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))))),
% 1.66/0.59    inference(definition_unfolding,[],[f38,f58,f43,f43])).
% 1.66/0.59  fof(f38,plain,(
% 1.66/0.59    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.66/0.59    inference(cnf_transformation,[],[f29])).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (10995)------------------------------
% 1.66/0.59  % (10995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (10995)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (10995)Memory used [KB]: 1918
% 1.66/0.59  % (10995)Time elapsed: 0.154 s
% 1.66/0.59  % (10995)------------------------------
% 1.66/0.59  % (10995)------------------------------
% 1.66/0.59  % (11011)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.66/0.59  % (10998)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.66/0.59  % (11000)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.66/0.59  % (10999)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.66/0.59  % (10994)Success in time 0.234 s
%------------------------------------------------------------------------------
