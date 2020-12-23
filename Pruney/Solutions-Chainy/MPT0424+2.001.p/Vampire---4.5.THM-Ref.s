%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  38 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   11
%              Number of atoms          :   52 (  94 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(global_subsumption,[],[f16,f33])).

fof(f33,plain,(
    r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f32,f15])).

fof(f15,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK2,sK1)
    & r2_hidden(sK2,sK0)
    & r1_tarski(k3_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,X1)
        & r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
   => ( ~ r1_tarski(sK2,sK1)
      & r2_hidden(sK2,sK0)
      & r1_tarski(k3_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          & r1_tarski(k3_tarski(X0),X1) )
       => r1_tarski(X2,X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f32,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f31,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f31,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,k3_tarski(sK0))
      | r1_tarski(X7,sK1) ) ),
    inference(superposition,[],[f20,f23])).

fof(f23,plain,(
    sK1 = k2_xboole_0(sK1,k3_tarski(sK0)) ),
    inference(superposition,[],[f21,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f21,plain,(
    sK1 = k2_xboole_0(k3_tarski(sK0),sK1) ),
    inference(resolution,[],[f19,f14])).

fof(f14,plain,(
    r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f16,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (1658)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (1655)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (1656)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (1655)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(global_subsumption,[],[f16,f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    r1_tarski(sK2,sK1)),
% 0.21/0.41    inference(resolution,[],[f32,f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    r2_hidden(sK2,sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => (~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1))),
% 0.21/0.41    inference(flattening,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & (r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.21/0.41    inference(negated_conjecture,[],[f5])).
% 0.21/0.41  fof(f5,conjecture,(
% 0.21/0.41    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.21/0.41  fof(f32,plain,(
% 0.21/0.41    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(X0,sK1)) )),
% 0.21/0.41    inference(resolution,[],[f31,f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    ( ! [X7] : (~r1_tarski(X7,k3_tarski(sK0)) | r1_tarski(X7,sK1)) )),
% 0.21/0.41    inference(superposition,[],[f20,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    sK1 = k2_xboole_0(sK1,k3_tarski(sK0))),
% 0.21/0.41    inference(superposition,[],[f21,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    sK1 = k2_xboole_0(k3_tarski(sK0),sK1)),
% 0.21/0.41    inference(resolution,[],[f19,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    r1_tarski(k3_tarski(sK0),sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ~r1_tarski(sK2,sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (1655)------------------------------
% 0.21/0.41  % (1655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (1655)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (1655)Memory used [KB]: 6012
% 0.21/0.41  % (1655)Time elapsed: 0.004 s
% 0.21/0.41  % (1655)------------------------------
% 0.21/0.41  % (1655)------------------------------
% 0.21/0.42  % (1650)Success in time 0.06 s
%------------------------------------------------------------------------------
