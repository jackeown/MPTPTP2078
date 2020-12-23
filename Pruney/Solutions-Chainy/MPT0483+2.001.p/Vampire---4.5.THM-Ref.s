%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   19 (  24 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  60 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(subsumption_resolution,[],[f22,f13])).

fof(f13,plain,(
    sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f22,plain,(
    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f21,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK0),X0)
      | sK0 = k5_relat_1(k6_relat_1(X0),sK0) ) ),
    inference(resolution,[],[f14,f12])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.53  % (17848)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (17847)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.53  % (17849)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (17864)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (17845)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (17848)Refutation not found, incomplete strategy% (17848)------------------------------
% 0.20/0.54  % (17848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17848)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (17848)Memory used [KB]: 6012
% 0.20/0.54  % (17848)Time elapsed: 0.113 s
% 0.20/0.54  % (17848)------------------------------
% 0.20/0.54  % (17848)------------------------------
% 0.20/0.54  % (17856)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (17858)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (17854)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (17864)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f22,f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) & v1_relat_1(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ? [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0 & v1_relat_1(X0)) => (sK0 != k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0) & v1_relat_1(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f5,plain,(
% 0.20/0.54    ? [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) != X0 & v1_relat_1(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.54    inference(negated_conjecture,[],[f3])).
% 0.20/0.54  fof(f3,conjecture,(
% 0.20/0.54    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    sK0 = k5_relat_1(k6_relat_1(k1_relat_1(sK0)),sK0)),
% 0.20/0.54    inference(resolution,[],[f21,f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f10])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(k1_relat_1(sK0),X0) | sK0 = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 0.20/0.54    inference(resolution,[],[f14,f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    v1_relat_1(sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,plain,(
% 0.20/0.54    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f6])).
% 0.20/0.54  fof(f6,plain,(
% 0.20/0.54    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (17864)------------------------------
% 0.20/0.54  % (17864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (17864)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (17864)Memory used [KB]: 6012
% 0.20/0.54  % (17864)Time elapsed: 0.117 s
% 0.20/0.54  % (17864)------------------------------
% 0.20/0.54  % (17864)------------------------------
% 0.20/0.54  % (17867)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (17855)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.54  % (17842)Success in time 0.184 s
%------------------------------------------------------------------------------
