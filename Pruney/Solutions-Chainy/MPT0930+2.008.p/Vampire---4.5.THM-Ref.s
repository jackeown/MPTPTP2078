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
% DateTime   : Thu Dec  3 12:59:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  91 expanded)
%              Number of leaves         :    5 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 353 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(global_subsumption,[],[f14,f29])).

fof(f29,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,(
    sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) ),
    inference(global_subsumption,[],[f13,f21])).

fof(f21,plain,
    ( sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f16,f14])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f13,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
      | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
    & r2_hidden(sK1,sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
            & r2_hidden(X1,X0) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
          & r2_hidden(X1,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0))
          | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0)) )
        & r2_hidden(X1,sK0) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
        | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) )
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            | ~ r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) )
          & r2_hidden(X1,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r2_hidden(X1,X0)
           => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
              & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r2_hidden(k2_mcart_1(X1),k2_relat_1(X0))
            & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

fof(f28,plain,(
    ! [X0] : ~ r2_hidden(k4_tarski(k1_mcart_1(sK1),X0),sK0) ),
    inference(global_subsumption,[],[f13,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(k1_mcart_1(sK1),X0),sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f26,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f26,plain,(
    ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(global_subsumption,[],[f14,f25])).

fof(f25,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(superposition,[],[f20,f24])).

fof(f20,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,k2_mcart_1(sK1)),sK0)
      | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ) ),
    inference(global_subsumption,[],[f13,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,k2_mcart_1(sK1)),sK0)
      | ~ v1_relat_1(sK0)
      | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f18,f15])).

fof(f15,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0))
    | ~ r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (17698)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.42  % (17697)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (17694)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  % (17694)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(global_subsumption,[],[f14,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0)),
% 0.20/0.43    inference(superposition,[],[f28,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1))),
% 0.20/0.43    inference(global_subsumption,[],[f13,f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    sK1 = k4_tarski(k1_mcart_1(sK1),k2_mcart_1(sK1)) | ~v1_relat_1(sK0)),
% 0.20/0.43    inference(resolution,[],[f16,f14])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(flattening,[],[f6])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0)) & v1_relat_1(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f11,f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0)) => (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) & v1_relat_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(sK0))) & r2_hidden(X1,sK0)) => ((~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) & r2_hidden(sK1,sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((~r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) | ~r2_hidden(k1_mcart_1(X1),k1_relat_1(X0))) & r2_hidden(X1,X0)) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f3])).
% 0.20/0.43  fof(f3,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r2_hidden(X1,X0) => (r2_hidden(k2_mcart_1(X1),k2_relat_1(X0)) & r2_hidden(k1_mcart_1(X1),k1_relat_1(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(k1_mcart_1(sK1),X0),sK0)) )),
% 0.20/0.43    inference(global_subsumption,[],[f13,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(k1_mcart_1(sK1),X0),sK0) | ~v1_relat_1(sK0)) )),
% 0.20/0.43    inference(resolution,[],[f26,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(flattening,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.20/0.43    inference(global_subsumption,[],[f14,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ~r2_hidden(sK1,sK0) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.20/0.43    inference(superposition,[],[f20,f24])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k2_mcart_1(sK1)),sK0) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) )),
% 0.20/0.43    inference(global_subsumption,[],[f13,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(k4_tarski(X0,k2_mcart_1(sK1)),sK0) | ~v1_relat_1(sK0) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))) )),
% 0.20/0.43    inference(resolution,[],[f18,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ~r2_hidden(k2_mcart_1(sK1),k2_relat_1(sK0)) | ~r2_hidden(k1_mcart_1(sK1),k1_relat_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    r2_hidden(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (17694)------------------------------
% 0.20/0.43  % (17694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (17694)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (17694)Memory used [KB]: 6140
% 0.20/0.43  % (17694)Time elapsed: 0.007 s
% 0.20/0.43  % (17694)------------------------------
% 0.20/0.43  % (17694)------------------------------
% 0.20/0.43  % (17689)Success in time 0.08 s
%------------------------------------------------------------------------------
