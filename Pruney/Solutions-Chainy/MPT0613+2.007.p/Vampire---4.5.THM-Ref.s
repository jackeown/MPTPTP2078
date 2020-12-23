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
% DateTime   : Thu Dec  3 12:51:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  76 expanded)
%              Number of leaves         :    6 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 299 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(resolution,[],[f42,f19])).

fof(f19,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ v4_relat_1(sK2,sK1)
    & v4_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v4_relat_1(X2,X1)
            & v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v4_relat_1(X2,sK1)
          & v4_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ v4_relat_1(X2,sK1)
        & v4_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v4_relat_1(sK2,sK1)
      & v4_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v4_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v4_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v4_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).

fof(f42,plain,(
    ! [X1] : ~ v4_relat_1(sK2,X1) ),
    inference(global_subsumption,[],[f20,f18,f40])).

fof(f40,plain,(
    ! [X1] :
      ( v4_relat_1(sK2,sK1)
      | ~ v4_relat_1(sK2,X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(superposition,[],[f24,f38])).

fof(f38,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f36,f27])).

fof(f27,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(global_subsumption,[],[f18,f26])).

fof(f26,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f36,plain,(
    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(resolution,[],[f33,f18])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK0),sK1) ) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k7_relat_1(X2,X0),X0)
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) )
      | ~ v4_relat_1(X2,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X1)
        & v1_relat_1(X2) )
     => ( v4_relat_1(k7_relat_1(X2,X0),X1)
        & v4_relat_1(k7_relat_1(X2,X0),X0)
        & v1_relat_1(k7_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).

fof(f18,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ~ v4_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:56:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (4533)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.42  % (4533)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(resolution,[],[f42,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    v4_relat_1(sK2,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    (~v4_relat_1(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2)) & r1_tarski(sK0,sK1)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1)) => (? [X2] : (~v4_relat_1(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) & r1_tarski(sK0,sK1))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ? [X2] : (~v4_relat_1(X2,sK1) & v4_relat_1(X2,sK0) & v1_relat_1(X2)) => (~v4_relat_1(sK2,sK1) & v4_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.22/0.42    inference(flattening,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0,X1] : (? [X2] : (~v4_relat_1(X2,X1) & (v4_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v4_relat_1(X2,X0) & v1_relat_1(X2)) => v4_relat_1(X2,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t217_relat_1)).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ( ! [X1] : (~v4_relat_1(sK2,X1)) )),
% 0.22/0.42    inference(global_subsumption,[],[f20,f18,f40])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ( ! [X1] : (v4_relat_1(sK2,sK1) | ~v4_relat_1(sK2,X1) | ~v1_relat_1(sK2)) )),
% 0.22/0.42    inference(superposition,[],[f24,f38])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    sK2 = k7_relat_1(sK2,sK1)),
% 0.22/0.42    inference(forward_demodulation,[],[f36,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    sK2 = k7_relat_1(sK2,sK0)),
% 0.22/0.42    inference(global_subsumption,[],[f18,f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.22/0.42    inference(resolution,[],[f21,f19])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    k7_relat_1(sK2,sK0) = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.42    inference(resolution,[],[f33,f18])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,sK0) = k7_relat_1(k7_relat_1(X0,sK0),sK1)) )),
% 0.22/0.42    inference(resolution,[],[f22,f17])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    r1_tarski(sK0,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X2) | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_relat_1)).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (v4_relat_1(k7_relat_1(X2,X0),X0) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | ~v4_relat_1(X2,X1) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))) | (~v4_relat_1(X2,X1) | ~v1_relat_1(X2)))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : ((v4_relat_1(X2,X1) & v1_relat_1(X2)) => (v4_relat_1(k7_relat_1(X2,X0),X1) & v4_relat_1(k7_relat_1(X2,X0),X0) & v1_relat_1(k7_relat_1(X2,X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc23_relat_1)).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    v1_relat_1(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ~v4_relat_1(sK2,sK1)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (4533)------------------------------
% 0.22/0.42  % (4533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (4533)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (4533)Memory used [KB]: 6140
% 0.22/0.42  % (4533)Time elapsed: 0.007 s
% 0.22/0.42  % (4533)------------------------------
% 0.22/0.42  % (4533)------------------------------
% 0.22/0.43  % (4528)Success in time 0.065 s
%------------------------------------------------------------------------------
