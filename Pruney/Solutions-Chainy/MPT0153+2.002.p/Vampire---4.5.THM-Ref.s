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
% DateTime   : Thu Dec  3 12:33:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 173 expanded)
%              Number of leaves         :   12 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 260 expanded)
%              Number of equality atoms :   42 ( 144 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f265,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,(
    k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(superposition,[],[f52,f222])).

fof(f222,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(superposition,[],[f176,f70])).

fof(f70,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(resolution,[],[f65,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f65,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2] :
      ( k1_xboole_0 != X2
      | r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f34,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f48,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X0) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f176,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k5_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f175,f49])).

fof(f175,plain,(
    ! [X0,X1] : k4_xboole_0(X1,X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f156,f51])).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f41,f49])).

fof(f156,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f43,f49])).

fof(f43,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38,f28])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f52,plain,(
    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f40,f49])).

fof(f40,plain,(
    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f27,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f23,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f17])).

fof(f17,plain,
    ( ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)
   => k1_tarski(sK0) != k2_tarski(sK0,sK0) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:12:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (30909)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (30909)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f265,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f264])).
% 0.22/0.48  fof(f264,plain,(
% 0.22/0.48    k1_tarski(sK0) != k1_tarski(sK0)),
% 0.22/0.48    inference(superposition,[],[f52,f222])).
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.22/0.48    inference(superposition,[],[f176,f70])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.22/0.48    inference(resolution,[],[f65,f33])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.48    inference(resolution,[],[f63,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f61])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.48    inference(resolution,[],[f60,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.48    inference(equality_resolution,[],[f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X2] : (k1_xboole_0 != X2 | r1_xboole_0(X2,X2)) )),
% 0.22/0.48    inference(superposition,[],[f34,f49])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(resolution,[],[f48,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.48    inference(nnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f42,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k4_xboole_0(X0,X0))) = X0) )),
% 0.22/0.48    inference(definition_unfolding,[],[f24,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f29,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f25,f38])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f176,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k5_xboole_0(k4_xboole_0(X1,X0),k1_xboole_0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f175,f49])).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X1,X0) = k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0)))) )),
% 0.22/0.48    inference(forward_demodulation,[],[f156,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.48    inference(backward_demodulation,[],[f41,f49])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(X1,X0))) = k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(X0,X0),k5_xboole_0(X0,k1_xboole_0)))) )),
% 0.22/0.48    inference(superposition,[],[f43,f49])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X0,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f38,f28])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.22/0.48    inference(backward_demodulation,[],[f40,f49])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK0),k1_tarski(sK0)))),
% 0.22/0.48    inference(definition_unfolding,[],[f23,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f27,f28])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0) => k1_tarski(sK0) != k2_tarski(sK0,sK0)),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : k1_tarski(X0) != k2_tarski(X0,X0)),
% 0.22/0.48    inference(ennf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,negated_conjecture,(
% 0.22/0.48    ~! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.48    inference(negated_conjecture,[],[f11])).
% 0.22/0.48  fof(f11,conjecture,(
% 0.22/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (30909)------------------------------
% 0.22/0.48  % (30909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (30909)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (30909)Memory used [KB]: 1791
% 0.22/0.48  % (30909)Time elapsed: 0.020 s
% 0.22/0.48  % (30909)------------------------------
% 0.22/0.48  % (30909)------------------------------
% 0.22/0.48  % (30895)Success in time 0.119 s
%------------------------------------------------------------------------------
