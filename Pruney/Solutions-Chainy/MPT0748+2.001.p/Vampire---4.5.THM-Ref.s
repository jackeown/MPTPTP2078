%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 252 expanded)
%              Number of leaves         :    8 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  113 ( 934 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f54])).

fof(f54,plain,(
    ! [X2] : r2_hidden(sK1(sK3(X2)),sK3(sK0)) ),
    inference(subsumption_resolution,[],[f52,f43])).

fof(f43,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(sK1(sK3(X1)))
      | r2_hidden(sK1(sK3(X1)),sK3(sK0)) ) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | r2_hidden(X2,sK3(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK3(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK3(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK3(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK3(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f36,plain,(
    ! [X1] : r2_hidden(sK1(sK3(X1)),sK0) ),
    inference(subsumption_resolution,[],[f34,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).

fof(f10,plain,
    ( ? [X0] :
      ! [X1] :
        ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
   => ! [X1] :
        ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( v3_ordinal1(X1)
           => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

fof(f34,plain,(
    ! [X1] :
      ( r2_hidden(sK1(sK3(X1)),sK0)
      | v3_ordinal1(sK1(sK3(X1))) ) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f13,f12])).

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

fof(f8,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
      | ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X0)
           => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(sK3(X0)))
      | r2_hidden(sK1(sK3(X0)),sK0) ) ),
    inference(resolution,[],[f28,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK3(X0))
      | v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | r2_hidden(sK1(X0),sK0) ) ),
    inference(resolution,[],[f20,f19])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(X0))
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X2] :
      ( r2_hidden(sK1(sK3(X2)),sK3(sK0))
      | v3_ordinal1(sK1(sK3(X2))) ) ),
    inference(resolution,[],[f47,f21])).

fof(f47,plain,(
    ! [X1] :
      ( v3_ordinal1(sK2(sK3(X1)))
      | r2_hidden(sK1(sK3(X1)),sK3(sK0)) ) ),
    inference(resolution,[],[f45,f25])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK3(X0)),sK3(X0))
      | r2_hidden(sK1(sK3(X0)),sK3(sK0)) ) ),
    inference(resolution,[],[f43,f20])).

fof(f143,plain,(
    ~ r2_hidden(sK1(sK3(sK0)),sK3(sK0)) ),
    inference(resolution,[],[f108,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f108,plain,(
    r1_tarski(sK3(sK0),sK1(sK3(sK0))) ),
    inference(resolution,[],[f86,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(X0))
      | r1_tarski(X0,sK1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,(
    v3_ordinal1(sK2(sK3(sK0))) ),
    inference(resolution,[],[f68,f25])).

fof(f68,plain,(
    r2_hidden(sK2(sK3(sK0)),sK3(sK0)) ),
    inference(resolution,[],[f54,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1(X0),X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(resolution,[],[f22,f27])).

fof(f22,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1(X0))
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:59:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.47  % (3184)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.47  % (3184)Refutation not found, incomplete strategy% (3184)------------------------------
% 0.22/0.47  % (3184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (3193)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.22/0.47  % (3184)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (3184)Memory used [KB]: 9722
% 0.22/0.47  % (3184)Time elapsed: 0.061 s
% 0.22/0.47  % (3184)------------------------------
% 0.22/0.47  % (3184)------------------------------
% 0.22/0.47  % (3189)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.47  % (3193)Refutation not found, incomplete strategy% (3193)------------------------------
% 0.22/0.47  % (3193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (3193)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (3193)Memory used [KB]: 9722
% 0.22/0.47  % (3193)Time elapsed: 0.062 s
% 0.22/0.47  % (3193)------------------------------
% 0.22/0.47  % (3193)------------------------------
% 0.22/0.49  % (3180)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (3180)Refutation not found, incomplete strategy% (3180)------------------------------
% 0.22/0.49  % (3180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (3180)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (3180)Memory used [KB]: 767
% 0.22/0.49  % (3180)Time elapsed: 0.027 s
% 0.22/0.49  % (3180)------------------------------
% 0.22/0.49  % (3180)------------------------------
% 0.22/0.49  % (3185)WARNING: option uwaf not known.
% 0.22/0.49  % (3185)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.49  % (3188)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.49  % (3194)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (3185)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f143,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(sK1(sK3(X2)),sK3(sK0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f52,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(sK1(sK3(X1))) | r2_hidden(sK1(sK3(X1)),sK3(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f36,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | r2_hidden(X2,sK3(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : ! [X2] : ((r2_hidden(X2,sK3(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK3(X0))))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK3(X0)) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,sK3(X0)))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | ~v3_ordinal1(X2) | ~r2_hidden(X2,X0)) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (~v3_ordinal1(X2) | ~r2_hidden(X2,X0))) & ((v3_ordinal1(X2) & r2_hidden(X2,X0)) | ~r2_hidden(X2,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK1(sK3(X1)),sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f34,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(X1) | r2_hidden(X1,sK0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X1] : (r2_hidden(X1,sK0) | ~v3_ordinal1(X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0] : ! [X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1)) => ! [X1] : (r2_hidden(X1,sK0) | ~v3_ordinal1(X1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ? [X0] : ! [X1] : (r2_hidden(X1,X0) | ~v3_ordinal1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ~! [X1] : (v3_ordinal1(X1) => r2_hidden(X1,X0))),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    ! [X0] : ~! [X1] : (v3_ordinal1(X1) => r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X1] : (r2_hidden(sK1(sK3(X1)),sK0) | v3_ordinal1(sK1(sK3(X1)))) )),
% 0.22/0.49    inference(resolution,[],[f29,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(sK2(X0)) | v3_ordinal1(sK1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : ((r1_tarski(X0,sK1(X0)) & v3_ordinal1(sK1(X0))) | (~v3_ordinal1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f8,f13,f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (r1_tarski(X0,X1) & v3_ordinal1(X1)) => (r1_tarski(X0,sK1(X0)) & v3_ordinal1(sK1(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (? [X2] : (~v3_ordinal1(X2) & r2_hidden(X2,X0)) => (~v3_ordinal1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : (r1_tarski(X0,X1) & v3_ordinal1(X1)) | ? [X2] : (~v3_ordinal1(X2) & r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ! [X0] : ~(! [X1] : (v3_ordinal1(X1) => ~r1_tarski(X0,X1)) & ! [X2] : (r2_hidden(X2,X0) => v3_ordinal1(X2)))),
% 0.22/0.49    inference(rectify,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : (v3_ordinal1(X1) => ~r1_tarski(X0,X1)) & ! [X1] : (r2_hidden(X1,X0) => v3_ordinal1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (v3_ordinal1(sK2(sK3(X0))) | r2_hidden(sK1(sK3(X0)),sK0)) )),
% 0.22/0.49    inference(resolution,[],[f28,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X2,X0] : (~r2_hidden(X2,sK3(X0)) | v3_ordinal1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | r2_hidden(sK1(X0),sK0)) )),
% 0.22/0.49    inference(resolution,[],[f20,f19])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0] : (v3_ordinal1(sK1(X0)) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2] : (r2_hidden(sK1(sK3(X2)),sK3(sK0)) | v3_ordinal1(sK1(sK3(X2)))) )),
% 0.22/0.49    inference(resolution,[],[f47,f21])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X1] : (v3_ordinal1(sK2(sK3(X1))) | r2_hidden(sK1(sK3(X1)),sK3(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f45,f25])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK2(sK3(X0)),sK3(X0)) | r2_hidden(sK1(sK3(X0)),sK3(sK0))) )),
% 0.22/0.49    inference(resolution,[],[f43,f20])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    ~r2_hidden(sK1(sK3(sK0)),sK3(sK0))),
% 0.22/0.49    inference(resolution,[],[f108,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    r1_tarski(sK3(sK0),sK1(sK3(sK0)))),
% 0.22/0.49    inference(resolution,[],[f86,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(sK2(X0)) | r1_tarski(X0,sK1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    v3_ordinal1(sK2(sK3(sK0)))),
% 0.22/0.49    inference(resolution,[],[f68,f25])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.50    r2_hidden(sK2(sK3(sK0)),sK3(sK0))),
% 0.22/0.50    inference(resolution,[],[f54,f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK1(X0),X0) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.50    inference(resolution,[],[f22,f27])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,sK1(X0)) | r2_hidden(sK2(X0),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (3185)------------------------------
% 0.22/0.50  % (3185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (3185)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (3185)Memory used [KB]: 895
% 0.22/0.50  % (3185)Time elapsed: 0.086 s
% 0.22/0.50  % (3185)------------------------------
% 0.22/0.50  % (3185)------------------------------
% 0.22/0.50  % (3174)Success in time 0.138 s
%------------------------------------------------------------------------------
