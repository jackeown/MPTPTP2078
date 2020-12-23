%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:59 EST 2020

% Result     : Theorem 1.11s
% Output     : Refutation 1.11s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f20,f13])).

fof(f13,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f20,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
      | X0 = X2 ) ),
    inference(resolution,[],[f17,f14])).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X2),X0)
      | ~ r1_tarski(X0,k1_tarski(X1))
      | X1 = X2 ) ),
    inference(resolution,[],[f16,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:21:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (2162)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.11/0.51  % (2159)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.11/0.51  % (2179)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.11/0.51  % (2160)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.11/0.51  % (2160)Refutation found. Thanks to Tanya!
% 1.11/0.51  % SZS status Theorem for theBenchmark
% 1.11/0.51  % SZS output start Proof for theBenchmark
% 1.11/0.51  fof(f22,plain,(
% 1.11/0.51    $false),
% 1.11/0.51    inference(subsumption_resolution,[],[f20,f13])).
% 1.11/0.51  fof(f13,plain,(
% 1.11/0.51    sK0 != sK2),
% 1.11/0.51    inference(cnf_transformation,[],[f11])).
% 1.11/0.51  fof(f11,plain,(
% 1.11/0.51    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.11/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10])).
% 1.11/0.51  fof(f10,plain,(
% 1.11/0.51    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 1.11/0.51    introduced(choice_axiom,[])).
% 1.11/0.51  fof(f6,plain,(
% 1.11/0.51    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.11/0.51    inference(ennf_transformation,[],[f5])).
% 1.11/0.51  fof(f5,negated_conjecture,(
% 1.11/0.51    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.11/0.51    inference(negated_conjecture,[],[f4])).
% 1.11/0.51  fof(f4,conjecture,(
% 1.11/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 1.11/0.51  fof(f20,plain,(
% 1.11/0.51    sK0 = sK2),
% 1.11/0.51    inference(resolution,[],[f18,f12])).
% 1.11/0.51  fof(f12,plain,(
% 1.11/0.51    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.11/0.51    inference(cnf_transformation,[],[f11])).
% 1.11/0.51  fof(f18,plain,(
% 1.11/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) | X0 = X2) )),
% 1.11/0.51    inference(resolution,[],[f17,f14])).
% 1.11/0.51  fof(f14,plain,(
% 1.11/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.11/0.51    inference(cnf_transformation,[],[f2])).
% 1.11/0.51  fof(f2,axiom,(
% 1.11/0.51    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.11/0.51  fof(f17,plain,(
% 1.11/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X2),X0) | ~r1_tarski(X0,k1_tarski(X1)) | X1 = X2) )),
% 1.11/0.51    inference(resolution,[],[f16,f15])).
% 1.11/0.51  fof(f15,plain,(
% 1.11/0.51    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.11/0.51    inference(cnf_transformation,[],[f7])).
% 1.11/0.51  fof(f7,plain,(
% 1.11/0.51    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.11/0.51    inference(ennf_transformation,[],[f3])).
% 1.11/0.51  fof(f3,axiom,(
% 1.11/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).
% 1.11/0.51  fof(f16,plain,(
% 1.11/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.11/0.51    inference(cnf_transformation,[],[f9])).
% 1.11/0.51  fof(f9,plain,(
% 1.11/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.11/0.51    inference(flattening,[],[f8])).
% 1.11/0.51  fof(f8,plain,(
% 1.11/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.11/0.51    inference(ennf_transformation,[],[f1])).
% 1.11/0.51  fof(f1,axiom,(
% 1.11/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.11/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.11/0.51  % SZS output end Proof for theBenchmark
% 1.11/0.51  % (2160)------------------------------
% 1.11/0.51  % (2160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.11/0.51  % (2160)Termination reason: Refutation
% 1.11/0.51  
% 1.11/0.51  % (2160)Memory used [KB]: 6012
% 1.11/0.51  % (2160)Time elapsed: 0.094 s
% 1.11/0.51  % (2160)------------------------------
% 1.11/0.51  % (2160)------------------------------
% 1.11/0.51  % (2171)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.11/0.51  % (2178)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.11/0.51  % (2155)Success in time 0.142 s
%------------------------------------------------------------------------------
