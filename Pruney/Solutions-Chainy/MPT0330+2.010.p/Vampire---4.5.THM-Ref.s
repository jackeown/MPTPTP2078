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
% DateTime   : Thu Dec  3 12:43:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 250 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :  113 ( 372 expanded)
%              Number of equality atoms :   14 ( 164 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(subsumption_resolution,[],[f712,f397])).

fof(f397,plain,(
    ! [X0,X1] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1)))) ),
    inference(superposition,[],[f165,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f25,f35,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f165,plain,(
    ! [X0,X1] : r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1)))) ),
    inference(resolution,[],[f83,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f35])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f83,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(sK3,X6)
      | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(X5,X5,X5,X5,sK2)),X6)) ) ),
    inference(superposition,[],[f61,f39])).

fof(f61,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X2)),X3))
      | ~ r1_tarski(sK3,X3) ) ),
    inference(resolution,[],[f51,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),sK3),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f49,f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK2,X0)
      | ~ r1_tarski(k2_zfmisc_1(X0,sK3),X1)
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(sK0,k2_zfmisc_1(X0,sK3))
      | ~ r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,sK3),X0)
      | r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f31,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f712,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(subsumption_resolution,[],[f711,f178])).

fof(f178,plain,(
    ! [X2,X3] : r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,sK4)),k3_tarski(k3_enumset1(X3,X3,X3,X3,sK5)))) ),
    inference(resolution,[],[f89,f82])).

fof(f82,plain,(
    ! [X4,X3] : r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3))) ),
    inference(superposition,[],[f38,f39])).

fof(f89,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(sK5,X18)
      | r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X17,X17,X17,X17,sK4)),X18)) ) ),
    inference(superposition,[],[f64,f39])).

fof(f64,plain,(
    ! [X2,X3] :
      ( r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X2)),X3))
      | ~ r1_tarski(sK5,X3) ) ),
    inference(resolution,[],[f52,f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X0)),sK5),X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4,X0)
      | ~ r1_tarski(k2_zfmisc_1(X0,sK5),X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f47,f31])).

fof(f47,plain,(
    ! [X1] :
      ( r1_tarski(sK1,k2_zfmisc_1(X1,sK5))
      | ~ r1_tarski(sK4,X1) ) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK4,sK5),X1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

fof(f711,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f37,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f23,f36,f36,f36])).

fof(f23,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (9832)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (9829)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (9824)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (9818)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (9821)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (9827)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (9816)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (9828)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (9815)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (9820)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (9831)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (9825)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (9822)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (9817)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (9819)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (9830)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (9823)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (9829)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f713,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f712,f397])).
% 0.21/0.53  fof(f397,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1))))) )),
% 0.21/0.53    inference(superposition,[],[f165,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f35,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f28,f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(X0,X0,X0,X0,sK2)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,X1))))) )),
% 0.21/0.53    inference(resolution,[],[f83,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f35])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X6,X5] : (~r1_tarski(sK3,X6) | r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(X5,X5,X5,X5,sK2)),X6))) )),
% 0.21/0.53    inference(superposition,[],[f61,f39])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X2)),X3)) | ~r1_tarski(sK3,X3)) )),
% 0.21/0.53    inference(resolution,[],[f51,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,X0)),sK3),X1) | r1_tarski(sK0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f49,f38])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(sK2,X0) | ~r1_tarski(k2_zfmisc_1(X0,sK3),X1) | r1_tarski(sK0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f46,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(sK0,k2_zfmisc_1(X0,sK3)) | ~r1_tarski(sK2,X0)) )),
% 0.21/0.53    inference(resolution,[],[f29,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(k2_zfmisc_1(sK2,sK3),X0) | r1_tarski(sK0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f31,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f13,f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f712,plain,(
% 0.21/0.53    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f711,f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X2,X2,X2,X2,sK4)),k3_tarski(k3_enumset1(X3,X3,X3,X3,sK5))))) )),
% 0.21/0.53    inference(resolution,[],[f89,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X4,X3] : (r1_tarski(X3,k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)))) )),
% 0.21/0.53    inference(superposition,[],[f38,f39])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X17,X18] : (~r1_tarski(sK5,X18) | r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(X17,X17,X17,X17,sK4)),X18))) )),
% 0.21/0.53    inference(superposition,[],[f64,f39])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X2)),X3)) | ~r1_tarski(sK5,X3)) )),
% 0.21/0.53    inference(resolution,[],[f52,f30])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(k3_tarski(k3_enumset1(sK4,sK4,sK4,sK4,X0)),sK5),X1) | r1_tarski(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f50,f38])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(sK4,X0) | ~r1_tarski(k2_zfmisc_1(X0,sK5),X1) | r1_tarski(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f47,f31])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(sK1,k2_zfmisc_1(X1,sK5)) | ~r1_tarski(sK4,X1)) )),
% 0.21/0.53    inference(resolution,[],[f29,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_tarski(k2_zfmisc_1(sK4,sK5),X1) | r1_tarski(sK1,X1)) )),
% 0.21/0.53    inference(resolution,[],[f31,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f711,plain,(
% 0.21/0.53    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.53    inference(resolution,[],[f37,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f32,f36])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK4)),k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,sK5))))),
% 0.21/0.53    inference(definition_unfolding,[],[f23,f36,f36,f36])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (9829)------------------------------
% 0.21/0.53  % (9829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9829)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (9829)Memory used [KB]: 7675
% 0.21/0.53  % (9829)Time elapsed: 0.111 s
% 0.21/0.53  % (9829)------------------------------
% 0.21/0.53  % (9829)------------------------------
% 0.21/0.53  % (9826)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (9814)Success in time 0.175 s
%------------------------------------------------------------------------------
