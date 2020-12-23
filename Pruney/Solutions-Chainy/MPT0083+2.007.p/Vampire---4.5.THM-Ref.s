%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:11 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 100 expanded)
%              Number of leaves         :    7 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   67 ( 170 expanded)
%              Number of equality atoms :   17 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f361,plain,(
    $false ),
    inference(resolution,[],[f360,f16])).

fof(f16,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

% (15206)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f360,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f356,f333])).

fof(f333,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X6,X7)
      | ~ r1_xboole_0(X7,X6) ) ),
    inference(trivial_inequality_removal,[],[f317])).

fof(f317,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X6,X7)
      | ~ r1_xboole_0(X7,X6) ) ),
    inference(superposition,[],[f33,f98])).

fof(f98,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X4))
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f356,plain,(
    ~ r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f351,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f351,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f333,f283])).

fof(f283,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(resolution,[],[f39,f113])).

fof(f113,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f96,f31])).

fof(f96,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f29,f31])).

fof(f29,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f17,f22,f22])).

fof(f17,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.07/0.28  % Computer   : n023.cluster.edu
% 0.07/0.28  % Model      : x86_64 x86_64
% 0.07/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.28  % Memory     : 8042.1875MB
% 0.07/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.28  % CPULimit   : 60
% 0.07/0.28  % WCLimit    : 600
% 0.07/0.28  % DateTime   : Tue Dec  1 15:26:20 EST 2020
% 0.07/0.28  % CPUTime    : 
% 0.15/0.41  % (15199)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.15/0.42  % (15211)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.15/0.43  % (15213)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.15/0.43  % (15210)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.15/0.43  % (15209)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.15/0.43  % (15205)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.15/0.43  % (15203)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.15/0.43  % (15202)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.15/0.43  % (15212)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.15/0.44  % (15204)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.15/0.44  % (15214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.15/0.44  % (15203)Refutation found. Thanks to Tanya!
% 0.15/0.44  % SZS status Theorem for theBenchmark
% 0.15/0.44  % SZS output start Proof for theBenchmark
% 0.15/0.44  fof(f361,plain,(
% 0.15/0.44    $false),
% 0.15/0.44    inference(resolution,[],[f360,f16])).
% 0.15/0.44  fof(f16,plain,(
% 0.15/0.44    r1_xboole_0(sK0,sK1)),
% 0.15/0.44    inference(cnf_transformation,[],[f14])).
% 0.15/0.44  fof(f14,plain,(
% 0.15/0.44    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 0.15/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 0.15/0.44  % (15206)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.15/0.44  fof(f13,plain,(
% 0.15/0.44    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 0.15/0.44    introduced(choice_axiom,[])).
% 0.15/0.44  fof(f11,plain,(
% 0.15/0.44    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.15/0.44    inference(ennf_transformation,[],[f10])).
% 0.15/0.44  fof(f10,negated_conjecture,(
% 0.15/0.44    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.15/0.44    inference(negated_conjecture,[],[f9])).
% 0.15/0.44  fof(f9,conjecture,(
% 0.15/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.15/0.44  fof(f360,plain,(
% 0.15/0.44    ~r1_xboole_0(sK0,sK1)),
% 0.15/0.44    inference(resolution,[],[f356,f333])).
% 0.15/0.44  fof(f333,plain,(
% 0.15/0.44    ( ! [X6,X7] : (r1_xboole_0(X6,X7) | ~r1_xboole_0(X7,X6)) )),
% 0.15/0.44    inference(trivial_inequality_removal,[],[f317])).
% 0.15/0.44  fof(f317,plain,(
% 0.15/0.44    ( ! [X6,X7] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X6,X7) | ~r1_xboole_0(X7,X6)) )),
% 0.15/0.44    inference(superposition,[],[f33,f98])).
% 0.15/0.44  fof(f98,plain,(
% 0.15/0.44    ( ! [X4,X5] : (k1_xboole_0 = k4_xboole_0(X5,k4_xboole_0(X5,X4)) | ~r1_xboole_0(X4,X5)) )),
% 0.15/0.44    inference(superposition,[],[f31,f34])).
% 0.15/0.44  fof(f34,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.15/0.44    inference(definition_unfolding,[],[f23,f22])).
% 0.15/0.44  fof(f22,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.15/0.44    inference(cnf_transformation,[],[f6])).
% 0.15/0.44  fof(f6,axiom,(
% 0.15/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.15/0.44  fof(f23,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.15/0.44    inference(cnf_transformation,[],[f15])).
% 0.15/0.44  fof(f15,plain,(
% 0.15/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.15/0.44    inference(nnf_transformation,[],[f2])).
% 0.15/0.44  fof(f2,axiom,(
% 0.15/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.15/0.44  fof(f31,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.15/0.44    inference(definition_unfolding,[],[f20,f22,f22])).
% 0.15/0.44  fof(f20,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.15/0.44    inference(cnf_transformation,[],[f1])).
% 0.15/0.44  fof(f1,axiom,(
% 0.15/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.15/0.44  fof(f33,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.15/0.44    inference(definition_unfolding,[],[f24,f22])).
% 0.15/0.44  fof(f24,plain,(
% 0.15/0.44    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.15/0.44    inference(cnf_transformation,[],[f15])).
% 0.15/0.44  fof(f356,plain,(
% 0.15/0.44    ~r1_xboole_0(sK1,sK0)),
% 0.15/0.44    inference(resolution,[],[f351,f39])).
% 0.15/0.44  fof(f39,plain,(
% 0.15/0.44    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X2,X0)) )),
% 0.15/0.44    inference(superposition,[],[f28,f32])).
% 0.15/0.44  fof(f32,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.15/0.44    inference(definition_unfolding,[],[f21,f22])).
% 0.15/0.44  fof(f21,plain,(
% 0.15/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.15/0.44    inference(cnf_transformation,[],[f3])).
% 0.15/0.44  fof(f3,axiom,(
% 0.15/0.44    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.15/0.44  fof(f28,plain,(
% 0.15/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.15/0.44    inference(cnf_transformation,[],[f12])).
% 0.15/0.44  fof(f12,plain,(
% 0.15/0.44    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.15/0.44    inference(ennf_transformation,[],[f8])).
% 0.15/0.44  fof(f8,axiom,(
% 0.15/0.44    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.15/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.15/0.44  fof(f351,plain,(
% 0.15/0.44    ~r1_xboole_0(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 0.15/0.44    inference(resolution,[],[f333,f283])).
% 0.15/0.44  fof(f283,plain,(
% 0.15/0.44    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK1)),
% 0.15/0.44    inference(resolution,[],[f39,f113])).
% 0.15/0.44  fof(f113,plain,(
% 0.15/0.44    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.15/0.44    inference(forward_demodulation,[],[f96,f31])).
% 0.15/0.44  fof(f96,plain,(
% 0.15/0.44    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.15/0.44    inference(backward_demodulation,[],[f29,f31])).
% 0.15/0.44  fof(f29,plain,(
% 0.15/0.44    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 0.15/0.44    inference(definition_unfolding,[],[f17,f22,f22])).
% 0.15/0.44  fof(f17,plain,(
% 0.15/0.44    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.15/0.44    inference(cnf_transformation,[],[f14])).
% 0.15/0.44  % SZS output end Proof for theBenchmark
% 0.15/0.44  % (15203)------------------------------
% 0.15/0.44  % (15203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.15/0.44  % (15203)Termination reason: Refutation
% 0.15/0.44  
% 0.15/0.44  % (15203)Memory used [KB]: 6268
% 0.15/0.44  % (15203)Time elapsed: 0.077 s
% 0.15/0.44  % (15203)------------------------------
% 0.15/0.44  % (15203)------------------------------
% 0.15/0.44  % (15198)Success in time 0.14 s
%------------------------------------------------------------------------------
