%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   34 (  92 expanded)
%              Number of leaves         :    7 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :   69 ( 183 expanded)
%              Number of equality atoms :   57 ( 171 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f73,f74])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(sK1,X0) ),
    inference(subsumption_resolution,[],[f71,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f71,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k1_xboole_0) != X0
      | ~ r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f27,f68])).

fof(f68,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f67,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f67,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f66])).

fof(f66,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(superposition,[],[f13,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f48,f12])).

fof(f48,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f13,f26])).

fof(f26,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f11,f25,f25])).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)
    | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f17,f25])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f73,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f37,f68])).

fof(f37,plain,(
    ! [X2] : r2_hidden(X2,k1_enumset1(X2,X2,X2)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_enumset1(X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (17442)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.49  % (17450)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.49  % (17456)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.50  % (17460)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.50  % (17460)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f73,f74])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    ( ! [X0] : (~r2_hidden(sK1,X0)) )),
% 0.19/0.50    inference(subsumption_resolution,[],[f71,f23])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.50  fof(f71,plain,(
% 0.19/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) != X0 | ~r2_hidden(sK1,X0)) )),
% 0.19/0.50    inference(superposition,[],[f27,f68])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f67,f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    k1_xboole_0 != sK0),
% 0.19/0.50    inference(cnf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.19/0.50    inference(ennf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.19/0.50    inference(negated_conjecture,[],[f8])).
% 0.19/0.50  fof(f8,conjecture,(
% 0.19/0.50    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f66])).
% 0.19/0.50  fof(f66,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f65])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.19/0.50    inference(superposition,[],[f13,f49])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.19/0.50    inference(subsumption_resolution,[],[f48,f12])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.19/0.50    inference(superposition,[],[f13,f26])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.19/0.50    inference(definition_unfolding,[],[f11,f25,f25])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.19/0.50    inference(definition_unfolding,[],[f22,f24])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) | k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f10])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.19/0.50    inference(definition_unfolding,[],[f17,f25])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.19/0.50    inference(cnf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,axiom,(
% 0.19/0.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    r2_hidden(sK1,k1_xboole_0)),
% 0.19/0.50    inference(superposition,[],[f37,f68])).
% 0.19/0.50  fof(f37,plain,(
% 0.19/0.50    ( ! [X2] : (r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 0.19/0.50    inference(equality_resolution,[],[f36])).
% 0.19/0.50  fof(f36,plain,(
% 0.19/0.50    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_enumset1(X2,X2,X2) != X1) )),
% 0.19/0.50    inference(equality_resolution,[],[f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 0.19/0.50    inference(definition_unfolding,[],[f18,f25])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (17460)------------------------------
% 0.19/0.50  % (17460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (17460)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (17460)Memory used [KB]: 1791
% 0.19/0.50  % (17460)Time elapsed: 0.111 s
% 0.19/0.50  % (17460)------------------------------
% 0.19/0.50  % (17460)------------------------------
% 0.19/0.50  % (17438)Success in time 0.148 s
%------------------------------------------------------------------------------
