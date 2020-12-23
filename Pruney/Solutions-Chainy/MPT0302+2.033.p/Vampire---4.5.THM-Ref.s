%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 163 expanded)
%              Number of leaves         :    4 (  36 expanded)
%              Depth                    :   15
%              Number of atoms          :   94 ( 469 expanded)
%              Number of equality atoms :   43 ( 311 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(subsumption_resolution,[],[f283,f13])).

fof(f13,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

fof(f283,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f276,f275])).

fof(f275,plain,(
    r2_hidden(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f272,f13])).

fof(f272,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | sK0 = sK1 ),
    inference(factoring,[],[f237])).

fof(f237,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0,sK1),X0)
      | r2_hidden(sK3(X0,sK1),sK0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f58,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X1,sK0) ) ),
    inference(superposition,[],[f18,f10])).

fof(f10,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f58,plain,(
    ! [X4,X3] :
      ( r2_hidden(k4_tarski(sK2(sK1),sK3(X3,X4)),k2_zfmisc_1(sK0,X4))
      | r2_hidden(sK3(X3,X4),X3)
      | X3 = X4 ) ),
    inference(resolution,[],[f27,f40])).

fof(f40,plain,(
    r2_hidden(sK2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f39,f11])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f34,f12])).

fof(f12,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | r2_hidden(sK2(sK1),sK0) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0),sK2(X1)),k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f26,f14])).

fof(f14,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,sK2(X2)),k2_zfmisc_1(X1,X2))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f19,f14])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | r2_hidden(k4_tarski(X3,sK3(X5,X6)),k2_zfmisc_1(X4,X6))
      | r2_hidden(sK3(X5,X6),X5)
      | X5 = X6 ) ),
    inference(resolution,[],[f19,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f276,plain,
    ( ~ r2_hidden(sK3(sK0,sK1),sK0)
    | sK0 = sK1 ),
    inference(resolution,[],[f275,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,sK1),sK0)
      | ~ r2_hidden(sK3(X0,sK1),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f77,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f77,plain,(
    ! [X5] :
      ( r2_hidden(X5,sK1)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(resolution,[],[f48,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f17,f10])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X2,X1] :
      ( r2_hidden(k4_tarski(X1,sK2(sK0)),k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f42,f19])).

fof(f42,plain,(
    r2_hidden(sK2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f41,f11])).

fof(f41,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0),sK1) ),
    inference(subsumption_resolution,[],[f35,f12])).

fof(f35,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | r2_hidden(sK2(sK0),sK1) ),
    inference(resolution,[],[f29,f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (22673)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (22657)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (22673)Refutation not found, incomplete strategy% (22673)------------------------------
% 0.21/0.50  % (22673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (22673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (22673)Memory used [KB]: 10746
% 0.21/0.50  % (22673)Time elapsed: 0.090 s
% 0.21/0.50  % (22673)------------------------------
% 0.21/0.50  % (22673)------------------------------
% 0.21/0.50  % (22657)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    sK0 != sK1),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    sK0 = sK1),
% 0.21/0.51    inference(subsumption_resolution,[],[f276,f275])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    r2_hidden(sK3(sK0,sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f272,f13])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    r2_hidden(sK3(sK0,sK1),sK0) | sK0 = sK1),
% 0.21/0.51    inference(factoring,[],[f237])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK3(X0,sK1),X0) | r2_hidden(sK3(X0,sK1),sK0) | sK1 = X0) )),
% 0.21/0.51    inference(resolution,[],[f58,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X1,sK0)) )),
% 0.21/0.51    inference(superposition,[],[f18,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X4,X3] : (r2_hidden(k4_tarski(sK2(sK1),sK3(X3,X4)),k2_zfmisc_1(sK0,X4)) | r2_hidden(sK3(X3,X4),X3) | X3 = X4) )),
% 0.21/0.51    inference(resolution,[],[f27,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    r2_hidden(sK2(sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f39,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | r2_hidden(sK2(sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f34,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | r2_hidden(sK2(sK1),sK0)),
% 0.21/0.51    inference(resolution,[],[f29,f21])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0),sK2(X1)),k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f26,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,sK2(X2)),k2_zfmisc_1(X1,X2)) | k1_xboole_0 = X2) )),
% 0.21/0.51    inference(resolution,[],[f19,f14])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X6,X4,X5,X3] : (~r2_hidden(X3,X4) | r2_hidden(k4_tarski(X3,sK3(X5,X6)),k2_zfmisc_1(X4,X6)) | r2_hidden(sK3(X5,X6),X5) | X5 = X6) )),
% 0.21/0.51    inference(resolution,[],[f19,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    ~r2_hidden(sK3(sK0,sK1),sK0) | sK0 = sK1),
% 0.21/0.51    inference(resolution,[],[f275,f81])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK3(X0,sK1),sK0) | ~r2_hidden(sK3(X0,sK1),X0) | sK1 = X0) )),
% 0.21/0.51    inference(resolution,[],[f77,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X5] : (r2_hidden(X5,sK1) | ~r2_hidden(X5,sK0)) )),
% 0.21/0.51    inference(resolution,[],[f48,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 0.21/0.51    inference(superposition,[],[f17,f10])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X1] : (r2_hidden(k4_tarski(X1,sK2(sK0)),k2_zfmisc_1(X2,sK1)) | ~r2_hidden(X1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f42,f19])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    r2_hidden(sK2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f41,f11])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | r2_hidden(sK2(sK0),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f12])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | r2_hidden(sK2(sK0),sK1)),
% 0.21/0.51    inference(resolution,[],[f29,f20])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (22657)------------------------------
% 0.21/0.51  % (22657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22657)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (22657)Memory used [KB]: 6524
% 0.21/0.51  % (22657)Time elapsed: 0.094 s
% 0.21/0.51  % (22657)------------------------------
% 0.21/0.51  % (22657)------------------------------
% 0.21/0.51  % (22650)Success in time 0.151 s
%------------------------------------------------------------------------------
