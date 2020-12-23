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
% DateTime   : Thu Dec  3 12:55:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  42 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 106 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f20,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f51,plain,(
    ~ r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f45,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f45,plain,(
    r1_tarski(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f36,plain,(
    r2_hidden(k1_ordinal1(k3_tarski(sK0)),sK0) ),
    inference(resolution,[],[f32,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X1] :
      ( ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f14,plain,
    ( ? [X0] :
      ! [X1] :
        ( ( r2_hidden(X1,X0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) )
   => ! [X1] :
        ( ( r2_hidden(X1,sK0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
    ! [X1] :
      ( ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f32,plain,(
    v3_ordinal1(k1_ordinal1(k3_tarski(sK0))) ),
    inference(resolution,[],[f27,f21])).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f27,plain,(
    v3_ordinal1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f26,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(sK1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ( ~ v3_ordinal1(sK1(X0))
        & r2_hidden(sK1(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v3_ordinal1(sK1(X0))
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v3_ordinal1(X1)
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(f26,plain,
    ( v3_ordinal1(sK1(sK0))
    | v3_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.45  % (17585)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.45  % (17579)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.46  % (17579)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(subsumption_resolution,[],[f51,f20])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.22/0.46  fof(f51,plain,(
% 0.22/0.46    ~r2_hidden(k3_tarski(sK0),k1_ordinal1(k3_tarski(sK0)))),
% 0.22/0.46    inference(resolution,[],[f45,f25])).
% 0.22/0.46  fof(f25,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,axiom,(
% 0.22/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    r1_tarski(k1_ordinal1(k3_tarski(sK0)),k3_tarski(sK0))),
% 0.22/0.46    inference(resolution,[],[f36,f24])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f11])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    r2_hidden(k1_ordinal1(k3_tarski(sK0)),sK0)),
% 0.22/0.46    inference(resolution,[],[f32,f19])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X1] : ((r2_hidden(X1,sK0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,sK0)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ? [X0] : ! [X1] : ((r2_hidden(X1,X0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,X0))) => ! [X1] : ((r2_hidden(X1,sK0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,sK0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ? [X0] : ! [X1] : ((r2_hidden(X1,X0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,X0)))),
% 0.22/0.46    inference(nnf_transformation,[],[f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ? [X0] : ! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,negated_conjecture,(
% 0.22/0.46    ~! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.46    inference(negated_conjecture,[],[f6])).
% 0.22/0.46  fof(f6,conjecture,(
% 0.22/0.46    ! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    v3_ordinal1(k1_ordinal1(k3_tarski(sK0)))),
% 0.22/0.46    inference(resolution,[],[f27,f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.46  fof(f27,plain,(
% 0.22/0.46    v3_ordinal1(k3_tarski(sK0))),
% 0.22/0.46    inference(subsumption_resolution,[],[f26,f23])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(sK1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | (~v3_ordinal1(sK1(X0)) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)) => (~v3_ordinal1(sK1(X0)) & r2_hidden(sK1(X0),X0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ? [X1] : (~v3_ordinal1(X1) & r2_hidden(X1,X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f4])).
% 0.22/0.46  fof(f4,axiom,(
% 0.22/0.46    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)) => v3_ordinal1(k3_tarski(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    v3_ordinal1(sK1(sK0)) | v3_ordinal1(k3_tarski(sK0))),
% 0.22/0.46    inference(resolution,[],[f18,f22])).
% 0.22/0.46  fof(f22,plain,(
% 0.22/0.46    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | r2_hidden(sK1(X0),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (17579)------------------------------
% 0.22/0.46  % (17579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (17579)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (17579)Memory used [KB]: 5373
% 0.22/0.46  % (17579)Time elapsed: 0.048 s
% 0.22/0.46  % (17579)------------------------------
% 0.22/0.46  % (17579)------------------------------
% 0.22/0.46  % (17571)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.46  % (17567)Success in time 0.103 s
%------------------------------------------------------------------------------
