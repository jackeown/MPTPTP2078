%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 104 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f20])).

fof(f20,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17,f16])).

fof(f16,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK0)
        & r2_hidden(X2,sK1) )
   => ( ~ r1_tarski(sK2,sK0)
      & r2_hidden(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).

% (16722)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
fof(f41,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(resolution,[],[f40,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_tarski(X0),sK0)
      | ~ r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | ~ r1_tarski(X0,sK0) ) ),
    inference(resolution,[],[f28,f21])).

fof(f21,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f40,plain,(
    r1_tarski(k3_tarski(sK1),sK0) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_setfam_1(X1,k1_tarski(X0))
      | r1_tarski(k3_tarski(X1),X0) ) ),
    inference(superposition,[],[f26,f22])).

fof(f22,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:33:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (16733)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (16723)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (16720)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (16723)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f41,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    r2_hidden(sK2,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f17,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) => (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.46    inference(negated_conjecture,[],[f9])).
% 0.21/0.46  fof(f9,conjecture,(
% 0.21/0.46    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.21/0.46  % (16722)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ~r2_hidden(sK2,sK1)),
% 0.21/0.46    inference(resolution,[],[f40,f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k3_tarski(X0),sK0) | ~r2_hidden(sK2,X0)) )),
% 0.21/0.46    inference(resolution,[],[f33,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(sK2,X0) | ~r1_tarski(X0,sK0)) )),
% 0.21/0.46    inference(resolution,[],[f28,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ~r1_tarski(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(sK1),sK0)),
% 0.21/0.47    inference(resolution,[],[f32,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_setfam_1(X1,k1_tarski(X0)) | r1_tarski(k3_tarski(X1),X0)) )),
% 0.21/0.47    inference(superposition,[],[f26,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (16723)------------------------------
% 0.21/0.47  % (16723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (16723)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (16723)Memory used [KB]: 1663
% 0.21/0.47  % (16723)Time elapsed: 0.054 s
% 0.21/0.47  % (16723)------------------------------
% 0.21/0.47  % (16723)------------------------------
% 0.21/0.47  % (16716)Success in time 0.105 s
%------------------------------------------------------------------------------
