%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 143 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(resolution,[],[f95,f17])).

fof(f17,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

% (27629)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f16,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ~ r2_hidden(sK2,sK1)
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ~ r2_hidden(sK2,sK1)
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
      & ~ r2_hidden(X2,X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f95,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f88,f18])).

fof(f18,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f80,f26])).

fof(f26,plain,(
    ~ r1_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK1) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f19,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(condensation,[],[f76])).

fof(f76,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(X4,X5)
      | r2_hidden(X6,X5)
      | r2_hidden(X7,X5)
      | r1_xboole_0(k2_xboole_0(k1_tarski(X6),k1_tarski(X7)),X5) ) ),
    inference(resolution,[],[f74,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3)
      | r1_xboole_0(k2_xboole_0(X0,X1),X3) ) ),
    inference(superposition,[],[f28,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

% (27643)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% (27647)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X1),X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f24,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),X3)
      | r2_hidden(X2,X3)
      | r2_hidden(X0,X3)
      | r2_hidden(X1,X3) ) ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k2_xboole_0(k1_tarski(X2),k2_xboole_0(X0,k1_tarski(X3))),X1)
      | r2_hidden(X3,X1)
      | r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f53,f22])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X0,X3)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k1_tarski(X2))),X3)
      | r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f27,f22])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(forward_demodulation,[],[f25,f23])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      | ~ r1_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:33:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (27640)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.46  % (27635)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (27630)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (27632)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (27630)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f103,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(resolution,[],[f95,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ~r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  % (27629)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1) & ~r2_hidden(sK2,sK1) & ~r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1)) => (~r1_xboole_0(k2_tarski(sK0,sK2),sK1) & ~r2_hidden(sK2,sK1) & ~r2_hidden(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f7])).
% 0.20/0.46  fof(f7,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(resolution,[],[f88,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ~r2_hidden(sK2,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    r2_hidden(sK2,sK1) | r2_hidden(sK0,sK1)),
% 0.20/0.46    inference(resolution,[],[f80,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ~r1_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK2)),sK1)),
% 0.20/0.46    inference(definition_unfolding,[],[f19,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X2)),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(condensation,[],[f76])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X6,X4,X7,X5] : (r2_hidden(X4,X5) | r2_hidden(X6,X5) | r2_hidden(X7,X5) | r1_xboole_0(k2_xboole_0(k1_tarski(X6),k1_tarski(X7)),X5)) )),
% 0.20/0.46    inference(resolution,[],[f74,f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3) | r1_xboole_0(k2_xboole_0(X0,X1),X3)) )),
% 0.20/0.46    inference(superposition,[],[f28,f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.20/0.47  % (27643)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (27647)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_xboole_0(X0,X1),X2) | r1_xboole_0(X0,X2)) )),
% 0.20/0.47    inference(resolution,[],[f24,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),X3) | r2_hidden(X2,X3) | r2_hidden(X0,X3) | r2_hidden(X1,X3)) )),
% 0.20/0.47    inference(resolution,[],[f59,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k2_xboole_0(k1_tarski(X2),k2_xboole_0(X0,k1_tarski(X3))),X1) | r2_hidden(X3,X1) | r2_hidden(X2,X1)) )),
% 0.20/0.47    inference(resolution,[],[f53,f22])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X0,X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,k1_tarski(X2))),X3) | r2_hidden(X2,X3)) )),
% 0.20/0.47    inference(resolution,[],[f27,f22])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | r1_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X2)),X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f25,f23])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) | ~r1_xboole_0(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) | ~r1_xboole_0(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) | (~r1_xboole_0(X2,X3) | ~r1_xboole_0(X1,X3) | ~r1_xboole_0(X0,X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_xboole_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (27630)------------------------------
% 0.20/0.47  % (27630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (27630)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (27630)Memory used [KB]: 1663
% 0.20/0.47  % (27630)Time elapsed: 0.046 s
% 0.20/0.47  % (27630)------------------------------
% 0.20/0.47  % (27630)------------------------------
% 0.20/0.47  % (27625)Success in time 0.118 s
%------------------------------------------------------------------------------
