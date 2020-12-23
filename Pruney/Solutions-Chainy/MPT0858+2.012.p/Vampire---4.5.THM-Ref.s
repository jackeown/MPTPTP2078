%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 139 expanded)
%              Number of leaves         :    7 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 185 expanded)
%              Number of equality atoms :   31 ( 141 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(subsumption_resolution,[],[f42,f45])).

fof(f45,plain,(
    sK2 != k2_mcart_1(sK0) ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( sK1 != sK1
    | sK2 != k2_mcart_1(sK0) ),
    inference(backward_demodulation,[],[f11,f41])).

fof(f41,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f25,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK2))) ),
    inference(definition_unfolding,[],[f12,f24,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f12,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k2_mcart_1(X0) != X2
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
       => ( k2_mcart_1(X0) = X2
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).

fof(f40,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X8,k2_enumset1(X7,X7,X7,X7))
      | X7 = X8 ) ),
    inference(superposition,[],[f32,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f15,f24,f24,f24])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f11,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(resolution,[],[f40,f33])).

fof(f33,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(resolution,[],[f25,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:10:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (24604)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (24608)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (24617)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (24608)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f42,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    sK2 != k2_mcart_1(sK0)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    sK1 != sK1 | sK2 != k2_mcart_1(sK0)),
% 0.20/0.52    inference(backward_demodulation,[],[f11,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    sK1 = k1_mcart_1(sK0)),
% 0.20/0.52    inference(resolution,[],[f40,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.52    inference(resolution,[],[f25,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK2)))),
% 0.20/0.52    inference(definition_unfolding,[],[f12,f24,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f13,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f14,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k1_tarski(sK2)))),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1,X2] : ((k2_mcart_1(X0) != X2 | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & k1_mcart_1(X0) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_mcart_1)).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X8,X7] : (~r2_hidden(X8,k2_enumset1(X7,X7,X7,X7)) | X7 = X8) )),
% 0.20/0.52    inference(superposition,[],[f32,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.20/0.52    inference(definition_unfolding,[],[f15,f24,f24,f24])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f21,f24])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    sK2 = k2_mcart_1(sK0)),
% 0.20/0.52    inference(resolution,[],[f40,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.20/0.52    inference(resolution,[],[f25,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (24608)------------------------------
% 0.20/0.52  % (24608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (24608)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (24608)Memory used [KB]: 6140
% 0.20/0.52  % (24608)Time elapsed: 0.106 s
% 0.20/0.52  % (24608)------------------------------
% 0.20/0.52  % (24608)------------------------------
% 0.20/0.52  % (24601)Success in time 0.16 s
%------------------------------------------------------------------------------
