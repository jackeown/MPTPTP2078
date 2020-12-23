%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 ( 111 expanded)
%              Number of leaves         :    6 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   78 ( 357 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f38,plain,(
    $false ),
    inference(subsumption_resolution,[],[f37,f28])).

fof(f28,plain,(
    r2_hidden(sK1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f26,f16])).

fof(f16,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1] :
      ( ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f10,plain,
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

fof(f9,plain,(
    ? [X0] :
    ! [X1] :
      ( ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f26,plain,
    ( r2_hidden(sK1(sK0),sK0)
    | v3_ordinal1(sK1(sK0)) ),
    inference(resolution,[],[f23,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(X0))
      | v3_ordinal1(sK1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( r1_tarski(X0,sK1(X0))
        & v3_ordinal1(sK1(X0)) )
      | ( ~ v3_ordinal1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f7,f13,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
     => ( r1_tarski(X0,sK1(X0))
        & v3_ordinal1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
     => ( ~ v3_ordinal1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
      | ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X0)
           => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_ordinal1)).

fof(f23,plain,
    ( v3_ordinal1(sK2(sK0))
    | r2_hidden(sK1(sK0),sK0) ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | r2_hidden(sK1(X0),sK0) ) ),
    inference(resolution,[],[f17,f16])).

fof(f17,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(X0))
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    ~ r2_hidden(sK1(sK0),sK0) ),
    inference(resolution,[],[f34,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f34,plain,(
    r1_tarski(sK0,sK1(sK0)) ),
    inference(resolution,[],[f33,f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(X0))
      | r1_tarski(X0,sK1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f33,plain,(
    v3_ordinal1(sK2(sK0)) ),
    inference(resolution,[],[f29,f15])).

fof(f29,plain,(
    r2_hidden(sK2(sK0),sK0) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0),X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(resolution,[],[f19,f21])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1(X0))
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (29800)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.48  % (29800)Refutation not found, incomplete strategy% (29800)------------------------------
% 0.22/0.48  % (29800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (29810)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.49  % (29816)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% 0.22/0.49  % (29807)WARNING: option uwaf not known.
% 0.22/0.49  % (29800)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (29800)Memory used [KB]: 9722
% 0.22/0.49  % (29800)Time elapsed: 0.050 s
% 0.22/0.49  % (29800)------------------------------
% 0.22/0.49  % (29800)------------------------------
% 0.22/0.49  % (29807)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.49  % (29807)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f37,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    r2_hidden(sK1(sK0),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f26,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X1] : ((r2_hidden(X1,sK0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,sK0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : ! [X1] : ((r2_hidden(X1,X0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,X0))) => ! [X1] : ((r2_hidden(X1,sK0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,sK0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : ! [X1] : ((r2_hidden(X1,X0) | ~v3_ordinal1(X1)) & (v3_ordinal1(X1) | ~r2_hidden(X1,X0)))),
% 0.22/0.49    inference(nnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0] : ! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f3])).
% 0.22/0.49  fof(f3,conjecture,(
% 0.22/0.49    ! [X0] : ~! [X1] : (r2_hidden(X1,X0) <=> v3_ordinal1(X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_ordinal1)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    r2_hidden(sK1(sK0),sK0) | v3_ordinal1(sK1(sK0))),
% 0.22/0.49    inference(resolution,[],[f23,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(sK2(X0)) | v3_ordinal1(sK1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : ((r1_tarski(X0,sK1(X0)) & v3_ordinal1(sK1(X0))) | (~v3_ordinal1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f7,f13,f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (r1_tarski(X0,X1) & v3_ordinal1(X1)) => (r1_tarski(X0,sK1(X0)) & v3_ordinal1(sK1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (? [X2] : (~v3_ordinal1(X2) & r2_hidden(X2,X0)) => (~v3_ordinal1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (r1_tarski(X0,X1) & v3_ordinal1(X1)) | ? [X2] : (~v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ! [X0] : ~(! [X1] : (v3_ordinal1(X1) => ~r1_tarski(X0,X1)) & ! [X2] : (r2_hidden(X2,X0) => v3_ordinal1(X2)))),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : (v3_ordinal1(X1) => ~r1_tarski(X0,X1)) & ! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_ordinal1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    v3_ordinal1(sK2(sK0)) | r2_hidden(sK1(sK0),sK0)),
% 0.22/0.49    inference(resolution,[],[f22,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X1] : (~r2_hidden(X1,sK0) | v3_ordinal1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | r2_hidden(sK1(X0),sK0)) )),
% 0.22/0.49    inference(resolution,[],[f17,f16])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0] : (v3_ordinal1(sK1(X0)) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ~r2_hidden(sK1(sK0),sK0)),
% 0.22/0.49    inference(resolution,[],[f34,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1(sK0))),
% 0.22/0.49    inference(resolution,[],[f33,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(sK2(X0)) | r1_tarski(X0,sK1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    v3_ordinal1(sK2(sK0))),
% 0.22/0.49    inference(resolution,[],[f29,f15])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    r2_hidden(sK2(sK0),sK0)),
% 0.22/0.50    inference(resolution,[],[f28,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK1(X0),X0) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.50    inference(resolution,[],[f19,f21])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,sK1(X0)) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (29807)------------------------------
% 0.22/0.50  % (29807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (29807)Termination reason: Refutation
% 0.22/0.50  % (29803)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.50  
% 0.22/0.50  % (29807)Memory used [KB]: 895
% 0.22/0.50  % (29807)Time elapsed: 0.067 s
% 0.22/0.50  % (29807)------------------------------
% 0.22/0.50  % (29807)------------------------------
% 0.22/0.50  % (29793)Success in time 0.131 s
%------------------------------------------------------------------------------
