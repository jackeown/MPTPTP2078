%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 154 expanded)
%              Number of leaves         :    7 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :   89 ( 226 expanded)
%              Number of equality atoms :   41 ( 141 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f18,f24,f24,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f58,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f57,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f15,f24])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f57,plain,(
    ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(subsumption_resolution,[],[f55,f36])).

fof(f36,plain,(
    r2_hidden(sK1,sK3) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,sK3) ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f25,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | r2_hidden(sK1,sK3) ),
    inference(definition_unfolding,[],[f12,f24])).

fof(f12,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <~> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
      <=> ( r2_hidden(X1,X3)
          & X0 = X2 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).

fof(f55,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(resolution,[],[f54,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f54,plain,(
    ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) ),
    inference(subsumption_resolution,[],[f53,f36])).

fof(f53,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,
    ( sK0 != sK0
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) ),
    inference(backward_demodulation,[],[f33,f48])).

fof(f48,plain,(
    sK0 = sK2 ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( sK0 = sK2
    | sK0 = sK2 ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,
    ( r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK0 = sK2 ),
    inference(resolution,[],[f26,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))
    | sK0 = sK2 ),
    inference(definition_unfolding,[],[f11,f24])).

fof(f11,plain,
    ( sK0 = sK2
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))
      | X1 = X2 ) ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X1] :
      ( k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X1,X1,X1,X1)
      | ~ r2_hidden(X2,k2_enumset1(X1,X1,X1,X1))
      | X1 = X2 ) ),
    inference(superposition,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f17,f24,f24,f24])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f33,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3)) ),
    inference(inner_rewriting,[],[f27])).

fof(f27,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f10,f24])).

fof(f10,plain,
    ( sK0 != sK2
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.53  % (21980)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (21964)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (21972)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (21981)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (21973)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (21964)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f58,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k4_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.55    inference(equality_resolution,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.21/0.55    inference(definition_unfolding,[],[f18,f24,f24,f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f13,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f14,f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.55    inference(resolution,[],[f57,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 0.21/0.55    inference(definition_unfolding,[],[f15,f24])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.55    inference(subsumption_resolution,[],[f55,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    r2_hidden(sK1,sK3)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    r2_hidden(sK1,sK3) | r2_hidden(sK1,sK3)),
% 0.21/0.55    inference(resolution,[],[f25,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | r2_hidden(sK1,sK3)),
% 0.21/0.55    inference(definition_unfolding,[],[f12,f24])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <~> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.55    inference(negated_conjecture,[],[f7])).
% 0.21/0.55  fof(f7,conjecture,(
% 0.21/0.55    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t128_zfmisc_1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK3) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.55    inference(resolution,[],[f54,f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))),
% 0.21/0.55    inference(subsumption_resolution,[],[f53,f36])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    sK0 != sK0 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))),
% 0.21/0.55    inference(backward_demodulation,[],[f33,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    sK0 = sK2),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    sK0 = sK2 | sK0 = sK2),
% 0.21/0.55    inference(resolution,[],[f45,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    r2_hidden(sK0,k2_enumset1(sK2,sK2,sK2,sK2)) | sK0 = sK2),
% 0.21/0.55    inference(resolution,[],[f26,f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)) | sK0 = sK2),
% 0.21/0.55    inference(definition_unfolding,[],[f11,f24])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    sK0 = sK2 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) | X1 = X2) )),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k2_enumset1(X1,X1,X1,X1) != k2_enumset1(X1,X1,X1,X1) | ~r2_hidden(X2,k2_enumset1(X1,X1,X1,X1)) | X1 = X2) )),
% 0.21/0.55    inference(superposition,[],[f28,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.21/0.55    inference(definition_unfolding,[],[f17,f24,f24,f24])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f16,f24])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK3))),
% 0.21/0.55    inference(inner_rewriting,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))),
% 0.21/0.55    inference(definition_unfolding,[],[f10,f24])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    sK0 != sK2 | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (21964)------------------------------
% 0.21/0.55  % (21964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21964)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (21964)Memory used [KB]: 6268
% 0.21/0.55  % (21964)Time elapsed: 0.127 s
% 0.21/0.55  % (21964)------------------------------
% 0.21/0.55  % (21964)------------------------------
% 0.21/0.55  % (21956)Success in time 0.194 s
%------------------------------------------------------------------------------
