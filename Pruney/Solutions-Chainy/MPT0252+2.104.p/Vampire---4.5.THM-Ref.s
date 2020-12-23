%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   21 (  26 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  62 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f48])).

fof(f48,plain,(
    ! [X0,X1] : ~ r1_tarski(k2_xboole_0(k2_tarski(sK0,X0),X1),sK2) ),
    inference(resolution,[],[f46,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(sK0,X1),X0)
      | ~ r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f28,f36])).

fof(f36,plain,(
    ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK2) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f21,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.42  % (30150)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.42  % (30150)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(subsumption_resolution,[],[f21,f48])).
% 0.22/0.42  fof(f48,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(sK0,X0),X1),sK2)) )),
% 0.22/0.42    inference(resolution,[],[f46,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(k2_tarski(sK0,X1),X0) | ~r1_tarski(X0,sK2)) )),
% 0.22/0.42    inference(resolution,[],[f28,f36])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,X0),sK2)) )),
% 0.22/0.42    inference(resolution,[],[f29,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ~r2_hidden(sK0,sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.22/0.42    inference(negated_conjecture,[],[f12])).
% 0.22/0.42  fof(f12,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.42    inference(flattening,[],[f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.42    inference(nnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f18])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (30150)------------------------------
% 0.22/0.42  % (30150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (30150)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (30150)Memory used [KB]: 6140
% 0.22/0.42  % (30150)Time elapsed: 0.004 s
% 0.22/0.42  % (30150)------------------------------
% 0.22/0.42  % (30150)------------------------------
% 0.22/0.42  % (30133)Success in time 0.068 s
%------------------------------------------------------------------------------
