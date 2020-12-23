%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:15 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 295 expanded)
%              Number of leaves         :   20 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  159 ( 386 expanded)
%              Number of equality atoms :   63 ( 274 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1762,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1761,f368])).

fof(f368,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(resolution,[],[f351,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f351,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f338,f349])).

fof(f349,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f323,f348])).

fof(f348,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f347,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f347,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9)))) ),
    inference(forward_demodulation,[],[f341,f66])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f341,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),X8))) ),
    inference(resolution,[],[f336,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f336,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(subsumption_resolution,[],[f325,f126])).

fof(f126,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f67,f66])).

fof(f325,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
      | r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) ),
    inference(superposition,[],[f87,f66])).

fof(f87,plain,(
    ! [X12,X11] :
      ( k4_xboole_0(X12,k4_xboole_0(X12,X11)) != X11
      | r1_xboole_0(X11,k4_xboole_0(X11,X12)) ) ),
    inference(superposition,[],[f48,f66])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f323,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f279,f126])).

fof(f279,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f126,f66])).

fof(f338,plain,(
    ! [X2,X0,X1] : r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1)) ),
    inference(resolution,[],[f336,f148])).

fof(f148,plain,(
    ! [X23,X21,X22] :
      ( ~ r1_xboole_0(X21,k4_xboole_0(X21,X22))
      | r1_xboole_0(X23,k4_xboole_0(X21,X22)) ) ),
    inference(backward_demodulation,[],[f91,f126])).

fof(f91,plain,(
    ! [X23,X21,X22] :
      ( r1_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X21))))
      | ~ r1_xboole_0(X21,k4_xboole_0(X21,X22)) ) ),
    inference(superposition,[],[f78,f66])).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4)))
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f68,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f39])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

% (30794)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1761,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f64,f1760])).

fof(f1760,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(resolution,[],[f73,f709])).

fof(f709,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f70,f65])).

fof(f65,plain,(
    ~ r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f34,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f64,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f35,f63,f39,f63])).

fof(f35,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (783056897)
% 0.20/0.36  ipcrm: permission denied for id (783089666)
% 0.20/0.36  ipcrm: permission denied for id (783122435)
% 0.20/0.36  ipcrm: permission denied for id (782696452)
% 0.20/0.36  ipcrm: permission denied for id (783155205)
% 0.20/0.37  ipcrm: permission denied for id (783187974)
% 0.20/0.37  ipcrm: permission denied for id (783220743)
% 0.20/0.37  ipcrm: permission denied for id (783253512)
% 0.20/0.37  ipcrm: permission denied for id (783286281)
% 0.20/0.37  ipcrm: permission denied for id (788889610)
% 0.20/0.37  ipcrm: permission denied for id (783351819)
% 0.20/0.37  ipcrm: permission denied for id (783417357)
% 0.20/0.37  ipcrm: permission denied for id (788955150)
% 0.20/0.38  ipcrm: permission denied for id (782761999)
% 0.20/0.38  ipcrm: permission denied for id (788987920)
% 0.20/0.38  ipcrm: permission denied for id (787283985)
% 0.20/0.38  ipcrm: permission denied for id (787316754)
% 0.20/0.38  ipcrm: permission denied for id (789020691)
% 0.20/0.38  ipcrm: permission denied for id (789053460)
% 0.20/0.38  ipcrm: permission denied for id (787447830)
% 0.20/0.39  ipcrm: permission denied for id (787513368)
% 0.20/0.39  ipcrm: permission denied for id (783777817)
% 0.20/0.39  ipcrm: permission denied for id (783810586)
% 0.20/0.39  ipcrm: permission denied for id (783843355)
% 0.20/0.39  ipcrm: permission denied for id (783876124)
% 0.20/0.39  ipcrm: permission denied for id (783908893)
% 0.20/0.39  ipcrm: permission denied for id (784007198)
% 0.20/0.40  ipcrm: permission denied for id (789151775)
% 0.20/0.40  ipcrm: permission denied for id (782827552)
% 0.20/0.40  ipcrm: permission denied for id (784039969)
% 0.20/0.40  ipcrm: permission denied for id (784072738)
% 0.20/0.40  ipcrm: permission denied for id (784105507)
% 0.20/0.40  ipcrm: permission denied for id (784138276)
% 0.20/0.40  ipcrm: permission denied for id (784171045)
% 0.20/0.40  ipcrm: permission denied for id (784203814)
% 0.20/0.41  ipcrm: permission denied for id (784236583)
% 0.20/0.41  ipcrm: permission denied for id (784269352)
% 0.20/0.41  ipcrm: permission denied for id (784302121)
% 0.20/0.41  ipcrm: permission denied for id (784334890)
% 0.20/0.41  ipcrm: permission denied for id (784367659)
% 0.20/0.41  ipcrm: permission denied for id (789184556)
% 0.20/0.41  ipcrm: permission denied for id (787611693)
% 0.20/0.41  ipcrm: permission denied for id (787644462)
% 0.20/0.41  ipcrm: permission denied for id (787677231)
% 0.20/0.42  ipcrm: permission denied for id (787710000)
% 0.20/0.42  ipcrm: permission denied for id (787742769)
% 0.20/0.42  ipcrm: permission denied for id (787775538)
% 0.20/0.42  ipcrm: permission denied for id (784695347)
% 0.20/0.42  ipcrm: permission denied for id (787808308)
% 0.20/0.42  ipcrm: permission denied for id (787841077)
% 0.20/0.42  ipcrm: permission denied for id (782893110)
% 0.20/0.42  ipcrm: permission denied for id (787873847)
% 0.20/0.43  ipcrm: permission denied for id (784793656)
% 0.20/0.43  ipcrm: permission denied for id (787906617)
% 0.20/0.43  ipcrm: permission denied for id (784859194)
% 0.20/0.43  ipcrm: permission denied for id (789217339)
% 0.20/0.43  ipcrm: permission denied for id (784924732)
% 0.20/0.43  ipcrm: permission denied for id (787972157)
% 0.20/0.43  ipcrm: permission denied for id (784990270)
% 0.20/0.43  ipcrm: permission denied for id (788004927)
% 0.20/0.44  ipcrm: permission denied for id (785055808)
% 0.20/0.44  ipcrm: permission denied for id (785088577)
% 0.20/0.44  ipcrm: permission denied for id (782925891)
% 0.20/0.44  ipcrm: permission denied for id (785154116)
% 0.20/0.44  ipcrm: permission denied for id (785219654)
% 0.20/0.44  ipcrm: permission denied for id (785252423)
% 0.20/0.45  ipcrm: permission denied for id (785285192)
% 0.20/0.45  ipcrm: permission denied for id (785350730)
% 0.20/0.45  ipcrm: permission denied for id (785383499)
% 0.20/0.45  ipcrm: permission denied for id (788136012)
% 0.20/0.45  ipcrm: permission denied for id (788168781)
% 0.20/0.45  ipcrm: permission denied for id (788201550)
% 0.20/0.45  ipcrm: permission denied for id (785547344)
% 0.20/0.46  ipcrm: permission denied for id (788267089)
% 0.20/0.46  ipcrm: permission denied for id (785612882)
% 0.20/0.46  ipcrm: permission denied for id (785645651)
% 0.20/0.46  ipcrm: permission denied for id (788299860)
% 0.20/0.46  ipcrm: permission denied for id (788332629)
% 0.20/0.46  ipcrm: permission denied for id (785743958)
% 0.20/0.46  ipcrm: permission denied for id (789413976)
% 0.20/0.47  ipcrm: permission denied for id (788430937)
% 0.20/0.47  ipcrm: permission denied for id (785875034)
% 0.20/0.47  ipcrm: permission denied for id (788463707)
% 0.20/0.47  ipcrm: permission denied for id (785940572)
% 0.20/0.47  ipcrm: permission denied for id (789446749)
% 0.20/0.47  ipcrm: permission denied for id (786006110)
% 0.20/0.47  ipcrm: permission denied for id (786038879)
% 0.20/0.47  ipcrm: permission denied for id (786071648)
% 0.20/0.48  ipcrm: permission denied for id (789479521)
% 0.20/0.48  ipcrm: permission denied for id (786137186)
% 0.20/0.48  ipcrm: permission denied for id (786169955)
% 0.20/0.48  ipcrm: permission denied for id (786202724)
% 0.20/0.48  ipcrm: permission denied for id (786235493)
% 0.20/0.48  ipcrm: permission denied for id (786268262)
% 0.20/0.48  ipcrm: permission denied for id (786301031)
% 0.20/0.48  ipcrm: permission denied for id (786333800)
% 0.20/0.49  ipcrm: permission denied for id (786366569)
% 0.20/0.49  ipcrm: permission denied for id (786399338)
% 0.20/0.49  ipcrm: permission denied for id (786432107)
% 0.20/0.49  ipcrm: permission denied for id (786464876)
% 0.20/0.49  ipcrm: permission denied for id (788594797)
% 0.20/0.49  ipcrm: permission denied for id (786530414)
% 0.20/0.49  ipcrm: permission denied for id (789512303)
% 0.20/0.49  ipcrm: permission denied for id (786595952)
% 0.20/0.49  ipcrm: permission denied for id (786628721)
% 0.20/0.50  ipcrm: permission denied for id (788660338)
% 0.20/0.50  ipcrm: permission denied for id (786694259)
% 0.20/0.50  ipcrm: permission denied for id (786727028)
% 0.20/0.50  ipcrm: permission denied for id (786792565)
% 0.20/0.50  ipcrm: permission denied for id (786825334)
% 0.20/0.50  ipcrm: permission denied for id (788693111)
% 0.20/0.50  ipcrm: permission denied for id (782991480)
% 0.20/0.50  ipcrm: permission denied for id (788725881)
% 0.20/0.51  ipcrm: permission denied for id (786923642)
% 0.20/0.51  ipcrm: permission denied for id (788824189)
% 0.20/0.51  ipcrm: permission denied for id (787054718)
% 0.20/0.51  ipcrm: permission denied for id (787087487)
% 0.69/0.58  % (30795)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.69/0.59  % (30803)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.69/0.62  % (30795)Refutation found. Thanks to Tanya!
% 0.69/0.62  % SZS status Theorem for theBenchmark
% 0.69/0.62  % SZS output start Proof for theBenchmark
% 0.69/0.62  fof(f1762,plain,(
% 0.69/0.62    $false),
% 0.69/0.62    inference(subsumption_resolution,[],[f1761,f368])).
% 0.69/0.62  fof(f368,plain,(
% 0.69/0.62    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.69/0.62    inference(resolution,[],[f351,f47])).
% 0.69/0.62  fof(f47,plain,(
% 0.69/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.69/0.62    inference(cnf_transformation,[],[f31])).
% 0.69/0.62  fof(f31,plain,(
% 0.69/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(nnf_transformation,[],[f7])).
% 0.69/0.62  fof(f7,axiom,(
% 0.69/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.69/0.62  fof(f351,plain,(
% 0.69/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.69/0.62    inference(backward_demodulation,[],[f338,f349])).
% 0.69/0.62  fof(f349,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.69/0.62    inference(backward_demodulation,[],[f323,f348])).
% 0.69/0.62  fof(f348,plain,(
% 0.69/0.62    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,X9))) )),
% 0.69/0.62    inference(forward_demodulation,[],[f347,f67])).
% 0.69/0.62  fof(f67,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.69/0.62    inference(definition_unfolding,[],[f40,f39])).
% 0.69/0.62  fof(f39,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(cnf_transformation,[],[f6])).
% 0.69/0.62  fof(f6,axiom,(
% 0.69/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.69/0.62  fof(f40,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f5])).
% 0.69/0.62  fof(f5,axiom,(
% 0.69/0.62    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.69/0.62  fof(f347,plain,(
% 0.69/0.62    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(X8,X9))))) )),
% 0.69/0.62    inference(forward_demodulation,[],[f341,f66])).
% 0.69/0.62  fof(f66,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.69/0.62    inference(definition_unfolding,[],[f37,f39,f39])).
% 0.69/0.62  fof(f37,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f1])).
% 0.69/0.62  fof(f1,axiom,(
% 0.69/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.69/0.62  fof(f341,plain,(
% 0.69/0.62    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(k4_xboole_0(X8,X9),X8)))) )),
% 0.69/0.62    inference(resolution,[],[f336,f72])).
% 0.69/0.62  fof(f72,plain,(
% 0.69/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(definition_unfolding,[],[f49,f39])).
% 0.69/0.62  fof(f49,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f32])).
% 0.69/0.62  fof(f32,plain,(
% 0.69/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(nnf_transformation,[],[f2])).
% 0.69/0.62  fof(f2,axiom,(
% 0.69/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.69/0.62  fof(f336,plain,(
% 0.69/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 0.69/0.62    inference(subsumption_resolution,[],[f325,f126])).
% 0.69/0.62  fof(f126,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.69/0.62    inference(superposition,[],[f67,f66])).
% 0.69/0.62  fof(f325,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) | r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) )),
% 0.69/0.62    inference(superposition,[],[f87,f66])).
% 0.69/0.62  fof(f87,plain,(
% 0.69/0.62    ( ! [X12,X11] : (k4_xboole_0(X12,k4_xboole_0(X12,X11)) != X11 | r1_xboole_0(X11,k4_xboole_0(X11,X12))) )),
% 0.69/0.62    inference(superposition,[],[f48,f66])).
% 0.69/0.62  fof(f48,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f31])).
% 0.69/0.62  fof(f323,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(forward_demodulation,[],[f279,f126])).
% 0.69/0.62  fof(f279,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) )),
% 0.69/0.62    inference(superposition,[],[f126,f66])).
% 0.69/0.62  fof(f338,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X2),X1))) )),
% 0.69/0.62    inference(resolution,[],[f336,f148])).
% 0.69/0.62  fof(f148,plain,(
% 0.69/0.62    ( ! [X23,X21,X22] : (~r1_xboole_0(X21,k4_xboole_0(X21,X22)) | r1_xboole_0(X23,k4_xboole_0(X21,X22))) )),
% 0.69/0.62    inference(backward_demodulation,[],[f91,f126])).
% 0.69/0.62  fof(f91,plain,(
% 0.69/0.62    ( ! [X23,X21,X22] : (r1_xboole_0(X23,k4_xboole_0(X21,k4_xboole_0(X22,k4_xboole_0(X22,X21)))) | ~r1_xboole_0(X21,k4_xboole_0(X21,X22))) )),
% 0.69/0.62    inference(superposition,[],[f78,f66])).
% 0.69/0.62  fof(f78,plain,(
% 0.69/0.62    ( ! [X4,X5,X3] : (r1_xboole_0(X5,k4_xboole_0(X3,k4_xboole_0(X3,X4))) | ~r1_xboole_0(X3,X4)) )),
% 0.69/0.62    inference(resolution,[],[f68,f44])).
% 0.69/0.62  fof(f44,plain,(
% 0.69/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f30])).
% 0.69/0.62  fof(f30,plain,(
% 0.69/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f29])).
% 0.69/0.62  fof(f29,plain,(
% 0.69/0.62    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.69/0.62    introduced(choice_axiom,[])).
% 0.69/0.62  fof(f23,plain,(
% 0.69/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(ennf_transformation,[],[f20])).
% 0.69/0.62  fof(f20,plain,(
% 0.69/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(rectify,[],[f3])).
% 0.69/0.62  fof(f3,axiom,(
% 0.69/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.69/0.62  fof(f68,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f42,f39])).
% 0.69/0.62  fof(f42,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.69/0.62    inference(cnf_transformation,[],[f28])).
% 0.69/0.62  fof(f28,plain,(
% 0.69/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f27])).
% 0.69/0.62  fof(f27,plain,(
% 0.69/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.69/0.62    introduced(choice_axiom,[])).
% 0.69/0.62  % (30794)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.69/0.62  fof(f22,plain,(
% 0.69/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(ennf_transformation,[],[f19])).
% 0.69/0.62  fof(f19,plain,(
% 0.69/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.69/0.62    inference(rectify,[],[f4])).
% 0.69/0.62  fof(f4,axiom,(
% 0.69/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.69/0.62  fof(f1761,plain,(
% 0.69/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.69/0.62    inference(backward_demodulation,[],[f64,f1760])).
% 0.69/0.62  fof(f1760,plain,(
% 0.69/0.62    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.69/0.62    inference(resolution,[],[f73,f709])).
% 0.69/0.62  fof(f709,plain,(
% 0.69/0.62    r2_hidden(sK0,sK1)),
% 0.69/0.62    inference(resolution,[],[f70,f65])).
% 0.69/0.62  fof(f65,plain,(
% 0.69/0.62    ~r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 0.69/0.62    inference(definition_unfolding,[],[f34,f63])).
% 0.69/0.62  fof(f63,plain,(
% 0.69/0.62    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f36,f62])).
% 0.69/0.62  fof(f62,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f38,f61])).
% 0.69/0.62  fof(f61,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f53,f60])).
% 0.69/0.62  fof(f60,plain,(
% 0.69/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f54,f59])).
% 0.69/0.62  fof(f59,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f55,f58])).
% 0.69/0.62  fof(f58,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f56,f57])).
% 0.69/0.62  fof(f57,plain,(
% 0.69/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f14])).
% 0.69/0.62  fof(f14,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.69/0.62  fof(f56,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f13])).
% 0.69/0.62  fof(f13,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.69/0.62  fof(f55,plain,(
% 0.69/0.62    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f12])).
% 0.69/0.62  fof(f12,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.69/0.62  fof(f54,plain,(
% 0.69/0.62    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f11])).
% 0.69/0.62  fof(f11,axiom,(
% 0.69/0.62    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.69/0.62  fof(f53,plain,(
% 0.69/0.62    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f10])).
% 0.69/0.62  fof(f10,axiom,(
% 0.69/0.62    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.69/0.62  fof(f38,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f9])).
% 0.69/0.62  fof(f9,axiom,(
% 0.69/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.69/0.62  fof(f36,plain,(
% 0.69/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f8])).
% 0.69/0.62  fof(f8,axiom,(
% 0.69/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.69/0.62  fof(f34,plain,(
% 0.69/0.62    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.69/0.62    inference(cnf_transformation,[],[f26])).
% 0.69/0.62  fof(f26,plain,(
% 0.69/0.62    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 0.69/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f25])).
% 0.69/0.62  fof(f25,plain,(
% 0.69/0.62    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 0.69/0.62    introduced(choice_axiom,[])).
% 0.69/0.62  fof(f21,plain,(
% 0.69/0.62    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.69/0.62    inference(ennf_transformation,[],[f18])).
% 0.69/0.62  fof(f18,negated_conjecture,(
% 0.69/0.62    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.69/0.62    inference(negated_conjecture,[],[f17])).
% 0.69/0.62  fof(f17,conjecture,(
% 0.69/0.62    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 0.69/0.62  fof(f70,plain,(
% 0.69/0.62    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f46,f63])).
% 0.69/0.62  fof(f46,plain,(
% 0.69/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f24])).
% 0.69/0.62  fof(f24,plain,(
% 0.69/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.69/0.62    inference(ennf_transformation,[],[f15])).
% 0.69/0.62  fof(f15,axiom,(
% 0.69/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.69/0.62  fof(f73,plain,(
% 0.69/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 0.69/0.62    inference(definition_unfolding,[],[f52,f63])).
% 0.69/0.62  fof(f52,plain,(
% 0.69/0.62    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.69/0.62    inference(cnf_transformation,[],[f33])).
% 0.69/0.62  fof(f33,plain,(
% 0.69/0.62    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.69/0.62    inference(nnf_transformation,[],[f16])).
% 0.69/0.62  fof(f16,axiom,(
% 0.69/0.62    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.69/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.69/0.62  fof(f64,plain,(
% 0.69/0.62    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 0.69/0.62    inference(definition_unfolding,[],[f35,f63,f39,f63])).
% 0.69/0.62  fof(f35,plain,(
% 0.69/0.62    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.69/0.62    inference(cnf_transformation,[],[f26])).
% 0.69/0.62  % SZS output end Proof for theBenchmark
% 0.69/0.62  % (30795)------------------------------
% 0.69/0.62  % (30795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.69/0.62  % (30795)Termination reason: Refutation
% 0.69/0.62  
% 0.69/0.62  % (30795)Memory used [KB]: 11385
% 0.69/0.62  % (30795)Time elapsed: 0.039 s
% 0.69/0.62  % (30795)------------------------------
% 0.69/0.62  % (30795)------------------------------
% 0.69/0.62  % (30652)Success in time 0.271 s
%------------------------------------------------------------------------------
