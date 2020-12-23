%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 132 expanded)
%              Number of leaves         :   10 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 208 expanded)
%              Number of equality atoms :   20 ( 128 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,sK1) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f48,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | r1_xboole_0(X0,sK1) ) ),
    inference(superposition,[],[f35,f45])).

fof(f45,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f41,f44])).

fof(f44,plain,(
    k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK0,sK0) ),
    inference(superposition,[],[f32,f41])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k2_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = k1_xboole_0
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f41,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).

fof(f20,plain,
    ( ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)
   => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f56,plain,(
    ~ r1_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f53,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f52,f45])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)
      | r2_hidden(sK0,X0) ) ),
    inference(superposition,[],[f36,f44])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f54,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (11676)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (11676)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f56,f49])).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,sK1)) )),
% 0.21/0.43    inference(subsumption_resolution,[],[f48,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | r1_xboole_0(X0,sK1)) )),
% 0.21/0.43    inference(superposition,[],[f35,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.43    inference(backward_demodulation,[],[f41,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK0,sK0)),
% 0.21/0.43    inference(superposition,[],[f32,f41])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ! [X0,X1] : (k1_xboole_0 = X0 | k2_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (k2_xboole_0(X0,X1) = k1_xboole_0 => k1_xboole_0 = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 0.21/0.43    inference(definition_unfolding,[],[f24,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f21])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) => k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,negated_conjecture,(
% 0.21/0.43    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.43    inference(negated_conjecture,[],[f10])).
% 0.21/0.43  fof(f10,conjecture,(
% 0.21/0.43    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ~r1_xboole_0(sK1,sK1)),
% 0.21/0.43    inference(resolution,[],[f55,f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(subsumption_resolution,[],[f53,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    ~r1_tarski(k1_xboole_0,sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.43    inference(superposition,[],[f52,f45])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) | r2_hidden(sK0,X0)) )),
% 0.21/0.43    inference(superposition,[],[f36,f44])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) | r2_hidden(X0,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f18])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_xboole_0(sK1,X0)) )),
% 0.21/0.43    inference(resolution,[],[f54,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(ennf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    inference(rectify,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (11676)------------------------------
% 0.21/0.43  % (11676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (11676)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (11676)Memory used [KB]: 6140
% 0.21/0.43  % (11676)Time elapsed: 0.026 s
% 0.21/0.43  % (11676)------------------------------
% 0.21/0.43  % (11676)------------------------------
% 0.21/0.43  % (11661)Success in time 0.075 s
%------------------------------------------------------------------------------
