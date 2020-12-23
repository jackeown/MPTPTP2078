%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 100 expanded)
%              Number of leaves         :    9 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 178 expanded)
%              Number of equality atoms :   24 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f85,plain,(
    $false ),
    inference(subsumption_resolution,[],[f84,f75])).

fof(f75,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f72,f68])).

fof(f68,plain,(
    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f33,plain,(
    r1_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f17,f20,f18,f20])).

fof(f18,plain,(
    sK0 = sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( X0 = X1
      & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( X0 = X1
          & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f20,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

fof(f17,plain,(
    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))
      | ~ r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f84,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f83,f82])).

fof(f82,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f40,f68])).

fof(f40,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f31,f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f83,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f81,f59])).

fof(f59,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f57,f42])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f29,f19])).

fof(f19,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f57,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(resolution,[],[f26,f19])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)
      | r2_hidden(sK1,X0) ) ),
    inference(superposition,[],[f34,f68])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f27,f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

% (16400)Refutation not found, incomplete strategy% (16400)------------------------------
% (16400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16400)Termination reason: Refutation not found, incomplete strategy

% (16400)Memory used [KB]: 10618
% (16400)Time elapsed: 0.103 s
% (16400)------------------------------
% (16400)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:52:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (16400)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (16412)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (16404)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (16412)Refutation not found, incomplete strategy% (16412)------------------------------
% 0.22/0.51  % (16412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16418)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (16412)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16412)Memory used [KB]: 10618
% 0.22/0.51  % (16412)Time elapsed: 0.064 s
% 0.22/0.51  % (16412)------------------------------
% 0.22/0.51  % (16412)------------------------------
% 0.22/0.52  % (16396)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (16410)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (16396)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f84,f75])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f72,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    k1_xboole_0 = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 0.22/0.52    inference(resolution,[],[f33,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    r1_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.52    inference(definition_unfolding,[],[f17,f20,f18,f20])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    sK0 = sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1] : (X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f70])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X0] : (~r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) | ~r2_hidden(X0,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) )),
% 0.22/0.52    inference(resolution,[],[f33,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    inference(rectify,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f83,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.22/0.52    inference(superposition,[],[f40,f68])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X1] : (r1_tarski(k1_xboole_0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f31,f20])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | r2_hidden(sK1,k1_xboole_0)),
% 0.22/0.52    inference(superposition,[],[f81,f59])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.22/0.52    inference(superposition,[],[f57,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(resolution,[],[f29,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) )),
% 0.22/0.52    inference(resolution,[],[f26,f19])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) | r2_hidden(sK1,X0)) )),
% 0.22/0.52    inference(superposition,[],[f34,f68])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X1),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f27,f20])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).
% 0.22/0.52  % (16400)Refutation not found, incomplete strategy% (16400)------------------------------
% 0.22/0.52  % (16400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16400)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (16400)Memory used [KB]: 10618
% 0.22/0.52  % (16400)Time elapsed: 0.103 s
% 0.22/0.52  % (16400)------------------------------
% 0.22/0.52  % (16400)------------------------------
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (16396)------------------------------
% 0.22/0.52  % (16396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (16396)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (16396)Memory used [KB]: 6268
% 0.22/0.52  % (16396)Time elapsed: 0.068 s
% 0.22/0.52  % (16396)------------------------------
% 0.22/0.52  % (16396)------------------------------
% 0.22/0.52  % (16408)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (16399)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (16389)Success in time 0.158 s
%------------------------------------------------------------------------------
