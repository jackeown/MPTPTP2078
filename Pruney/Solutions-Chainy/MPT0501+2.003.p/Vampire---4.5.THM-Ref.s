%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   19 (  30 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :    8
%              Number of atoms          :   37 (  62 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,plain,(
    $false ),
    inference(resolution,[],[f20,f12])).

fof(f12,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

fof(f20,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1)) ),
    inference(global_subsumption,[],[f11,f13,f18])).

fof(f18,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f14,f16])).

fof(f16,plain,(
    ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    inference(resolution,[],[f15,f11])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f13,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (32489)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.42  % (32488)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.42  % (32491)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (32488)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(resolution,[],[f20,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))) )),
% 0.22/0.42    inference(global_subsumption,[],[f11,f13,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(superposition,[],[f14,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) )),
% 0.22/0.42    inference(resolution,[],[f15,f11])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    v1_relat_1(sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (32488)------------------------------
% 0.22/0.42  % (32488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (32488)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (32488)Memory used [KB]: 6012
% 0.22/0.42  % (32488)Time elapsed: 0.003 s
% 0.22/0.42  % (32488)------------------------------
% 0.22/0.42  % (32488)------------------------------
% 0.22/0.42  % (32483)Success in time 0.062 s
%------------------------------------------------------------------------------
