%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:00 EST 2020

% Result     : Theorem 2.39s
% Output     : Refutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 107 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 184 expanded)
%              Number of equality atoms :   16 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6824,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6823,f775])).

fof(f775,plain,(
    ! [X12] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X12)),sK3)) ),
    inference(superposition,[],[f83,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f25,f23,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f83,plain,(
    ! [X1] : r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X1))) ),
    inference(superposition,[],[f44,f40])).

fof(f40,plain,(
    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3))) ),
    inference(resolution,[],[f31,f18])).

fof(f18,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2))) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2)
      | r1_tarski(X0,X2) ) ),
    inference(definition_unfolding,[],[f27,f23])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f6823,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) ),
    inference(subsumption_resolution,[],[f6775,f795])).

fof(f795,plain,(
    ! [X54] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X54,sK4)),sK5)) ),
    inference(superposition,[],[f107,f33])).

fof(f107,plain,(
    ! [X2] : r1_tarski(sK1,k3_tarski(k2_tarski(X2,k2_zfmisc_1(sK4,sK5)))) ),
    inference(superposition,[],[f45,f41])).

fof(f41,plain,(
    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f31,f19])).

fof(f19,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X4,X5,X3] : r1_tarski(X3,k3_tarski(k2_tarski(X4,k3_tarski(k2_tarski(X3,X5))))) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f6775,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3)) ),
    inference(resolution,[],[f1030,f29])).

fof(f29,plain,(
    ~ r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5)))) ),
    inference(definition_unfolding,[],[f20,f23,f23,f23])).

fof(f20,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f17])).

fof(f1030,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( r1_tarski(k3_tarski(k2_tarski(X7,X8)),k2_zfmisc_1(X4,k3_tarski(k2_tarski(X5,X6))))
      | ~ r1_tarski(X8,k2_zfmisc_1(X4,X6))
      | ~ r1_tarski(X7,k2_zfmisc_1(X4,X5)) ) ),
    inference(superposition,[],[f35,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f26,f23,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f23,f23])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:50:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (8002)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (7994)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (8001)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (7998)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (7997)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (7996)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (7990)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.49  % (7991)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (7992)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (8004)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (7993)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (7995)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (8000)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (7989)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (7999)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (8003)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (7988)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (8005)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.39/0.69  % (7997)Refutation found. Thanks to Tanya!
% 2.39/0.69  % SZS status Theorem for theBenchmark
% 2.39/0.69  % SZS output start Proof for theBenchmark
% 2.39/0.69  fof(f6824,plain,(
% 2.39/0.69    $false),
% 2.39/0.69    inference(subsumption_resolution,[],[f6823,f775])).
% 2.39/0.69  fof(f775,plain,(
% 2.39/0.69    ( ! [X12] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,X12)),sK3))) )),
% 2.39/0.69    inference(superposition,[],[f83,f33])).
% 2.39/0.69  fof(f33,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k2_tarski(X0,X1)),X2) = k3_tarski(k2_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 2.39/0.69    inference(definition_unfolding,[],[f25,f23,f23])).
% 2.39/0.69  fof(f23,plain,(
% 2.39/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.39/0.69    inference(cnf_transformation,[],[f6])).
% 2.39/0.69  fof(f6,axiom,(
% 2.39/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.39/0.69  fof(f25,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 2.39/0.69    inference(cnf_transformation,[],[f7])).
% 2.39/0.69  fof(f7,axiom,(
% 2.39/0.69    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 2.39/0.69  fof(f83,plain,(
% 2.39/0.69    ( ! [X1] : (r1_tarski(sK0,k3_tarski(k2_tarski(k2_zfmisc_1(sK2,sK3),X1)))) )),
% 2.39/0.69    inference(superposition,[],[f44,f40])).
% 2.39/0.69  fof(f40,plain,(
% 2.39/0.69    k2_zfmisc_1(sK2,sK3) = k3_tarski(k2_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 2.39/0.69    inference(resolution,[],[f31,f18])).
% 2.39/0.69  fof(f18,plain,(
% 2.39/0.69    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.39/0.69    inference(cnf_transformation,[],[f17])).
% 2.39/0.69  fof(f17,plain,(
% 2.39/0.69    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 2.39/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f16])).
% 2.39/0.69  fof(f16,plain,(
% 2.39/0.69    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 2.39/0.69    introduced(choice_axiom,[])).
% 2.39/0.69  fof(f11,plain,(
% 2.39/0.69    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 2.39/0.69    inference(flattening,[],[f10])).
% 2.39/0.69  fof(f10,plain,(
% 2.39/0.69    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 2.39/0.69    inference(ennf_transformation,[],[f9])).
% 2.39/0.69  fof(f9,negated_conjecture,(
% 2.39/0.69    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.39/0.69    inference(negated_conjecture,[],[f8])).
% 2.39/0.69  fof(f8,conjecture,(
% 2.39/0.69    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 2.39/0.69  fof(f31,plain,(
% 2.39/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 2.39/0.69    inference(definition_unfolding,[],[f24,f23])).
% 2.39/0.69  fof(f24,plain,(
% 2.39/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.39/0.69    inference(cnf_transformation,[],[f12])).
% 2.39/0.69  fof(f12,plain,(
% 2.39/0.69    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.39/0.69    inference(ennf_transformation,[],[f2])).
% 2.39/0.69  fof(f2,axiom,(
% 2.39/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.39/0.69  fof(f44,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(k3_tarski(k2_tarski(X0,X1)),X2)))) )),
% 2.39/0.69    inference(resolution,[],[f34,f30])).
% 2.39/0.69  fof(f30,plain,(
% 2.39/0.69    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 2.39/0.69    inference(definition_unfolding,[],[f21,f23])).
% 2.39/0.69  fof(f21,plain,(
% 2.39/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.39/0.69    inference(cnf_transformation,[],[f4])).
% 2.39/0.69  fof(f4,axiom,(
% 2.39/0.69    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.39/0.69  fof(f34,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(k2_tarski(X0,X1)),X2) | r1_tarski(X0,X2)) )),
% 2.39/0.69    inference(definition_unfolding,[],[f27,f23])).
% 2.39/0.69  fof(f27,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.39/0.69    inference(cnf_transformation,[],[f13])).
% 2.39/0.69  fof(f13,plain,(
% 2.39/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.39/0.69    inference(ennf_transformation,[],[f1])).
% 2.39/0.69  fof(f1,axiom,(
% 2.39/0.69    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.39/0.69  fof(f6823,plain,(
% 2.39/0.69    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))),
% 2.39/0.69    inference(subsumption_resolution,[],[f6775,f795])).
% 2.39/0.69  fof(f795,plain,(
% 2.39/0.69    ( ! [X54] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(X54,sK4)),sK5))) )),
% 2.39/0.69    inference(superposition,[],[f107,f33])).
% 2.39/0.69  fof(f107,plain,(
% 2.39/0.69    ( ! [X2] : (r1_tarski(sK1,k3_tarski(k2_tarski(X2,k2_zfmisc_1(sK4,sK5))))) )),
% 2.39/0.69    inference(superposition,[],[f45,f41])).
% 2.39/0.69  fof(f41,plain,(
% 2.39/0.69    k2_zfmisc_1(sK4,sK5) = k3_tarski(k2_tarski(sK1,k2_zfmisc_1(sK4,sK5)))),
% 2.39/0.69    inference(resolution,[],[f31,f19])).
% 2.39/0.69  fof(f19,plain,(
% 2.39/0.69    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 2.39/0.69    inference(cnf_transformation,[],[f17])).
% 2.39/0.69  fof(f45,plain,(
% 2.39/0.69    ( ! [X4,X5,X3] : (r1_tarski(X3,k3_tarski(k2_tarski(X4,k3_tarski(k2_tarski(X3,X5)))))) )),
% 2.39/0.69    inference(resolution,[],[f34,f36])).
% 2.39/0.69  fof(f36,plain,(
% 2.39/0.69    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 2.39/0.69    inference(superposition,[],[f30,f22])).
% 2.39/0.69  fof(f22,plain,(
% 2.39/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.39/0.69    inference(cnf_transformation,[],[f5])).
% 2.39/0.69  fof(f5,axiom,(
% 2.39/0.69    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.39/0.69  fof(f6775,plain,(
% 2.39/0.69    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK5)) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),sK3))),
% 2.39/0.69    inference(resolution,[],[f1030,f29])).
% 2.39/0.69  fof(f29,plain,(
% 2.39/0.69    ~r1_tarski(k3_tarski(k2_tarski(sK0,sK1)),k2_zfmisc_1(k3_tarski(k2_tarski(sK2,sK4)),k3_tarski(k2_tarski(sK3,sK5))))),
% 2.39/0.69    inference(definition_unfolding,[],[f20,f23,f23,f23])).
% 2.39/0.69  fof(f20,plain,(
% 2.39/0.69    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 2.39/0.69    inference(cnf_transformation,[],[f17])).
% 2.39/0.69  fof(f1030,plain,(
% 2.39/0.69    ( ! [X6,X4,X8,X7,X5] : (r1_tarski(k3_tarski(k2_tarski(X7,X8)),k2_zfmisc_1(X4,k3_tarski(k2_tarski(X5,X6)))) | ~r1_tarski(X8,k2_zfmisc_1(X4,X6)) | ~r1_tarski(X7,k2_zfmisc_1(X4,X5))) )),
% 2.39/0.69    inference(superposition,[],[f35,f32])).
% 2.39/0.69  fof(f32,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 2.39/0.69    inference(definition_unfolding,[],[f26,f23,f23])).
% 2.39/0.69  fof(f26,plain,(
% 2.39/0.69    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 2.39/0.69    inference(cnf_transformation,[],[f7])).
% 2.39/0.69  fof(f35,plain,(
% 2.39/0.69    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),k3_tarski(k2_tarski(X1,X3))) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.39/0.69    inference(definition_unfolding,[],[f28,f23,f23])).
% 2.39/0.69  fof(f28,plain,(
% 2.39/0.69    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 2.39/0.69    inference(cnf_transformation,[],[f15])).
% 2.39/0.69  fof(f15,plain,(
% 2.39/0.69    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.39/0.69    inference(flattening,[],[f14])).
% 2.39/0.69  fof(f14,plain,(
% 2.39/0.69    ! [X0,X1,X2,X3] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.39/0.69    inference(ennf_transformation,[],[f3])).
% 2.39/0.69  fof(f3,axiom,(
% 2.39/0.69    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 2.39/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).
% 2.39/0.69  % SZS output end Proof for theBenchmark
% 2.39/0.69  % (7997)------------------------------
% 2.39/0.69  % (7997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.69  % (7997)Termination reason: Refutation
% 2.39/0.69  
% 2.39/0.69  % (7997)Memory used [KB]: 19189
% 2.39/0.69  % (7997)Time elapsed: 0.275 s
% 2.39/0.69  % (7997)------------------------------
% 2.39/0.69  % (7997)------------------------------
% 2.39/0.70  % (7987)Success in time 0.323 s
%------------------------------------------------------------------------------
