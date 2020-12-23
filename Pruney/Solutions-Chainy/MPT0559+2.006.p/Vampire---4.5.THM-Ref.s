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
% DateTime   : Thu Dec  3 12:49:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  51 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 ( 113 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f29])).

fof(f29,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f28,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f28,plain,(
    ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    ! [X0] : r1_tarski(k7_relat_1(sK2,X0),sK2) ),
    inference(global_subsumption,[],[f15,f24])).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(k7_relat_1(sK2,X0),sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f20,f22])).

fof(f22,plain,(
    ! [X0] : k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0) ),
    inference(resolution,[],[f18,f15])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).

fof(f27,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(global_subsumption,[],[f15,f26])).

fof(f26,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f21,f16])).

fof(f16,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:54:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (1488)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.43  % (1483)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (1483)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(global_subsumption,[],[f15,f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ~v1_relat_1(sK2)),
% 0.22/0.43    inference(resolution,[],[f28,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.43    inference(resolution,[],[f27,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2)) )),
% 0.22/0.43    inference(global_subsumption,[],[f15,f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ( ! [X0] : (r1_tarski(k7_relat_1(sK2,X0),sK2) | ~v1_relat_1(sK2)) )),
% 0.22/0.43    inference(superposition,[],[f20,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0] : (k5_relat_1(k6_relat_1(X0),sK2) = k7_relat_1(sK2,X0)) )),
% 0.22/0.43    inference(resolution,[],[f18,f15])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f10])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_relat_1)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.43    inference(global_subsumption,[],[f15,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ~r1_tarski(k7_relat_1(sK2,sK0),sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.43    inference(resolution,[],[f21,f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f5])).
% 0.22/0.43  fof(f5,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    v1_relat_1(sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (1483)------------------------------
% 0.22/0.43  % (1483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (1483)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (1483)Memory used [KB]: 6140
% 0.22/0.43  % (1483)Time elapsed: 0.003 s
% 0.22/0.43  % (1483)------------------------------
% 0.22/0.43  % (1483)------------------------------
% 0.22/0.43  % (1478)Success in time 0.065 s
%------------------------------------------------------------------------------
