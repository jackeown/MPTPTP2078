%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:42 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   32 (  64 expanded)
%              Number of leaves         :    7 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 229 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f17,f54])).

fof(f54,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f53,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f53,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK0) ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    ! [X6] :
      ( r1_tarski(X6,sK1)
      | ~ r1_tarski(X6,sK0) ) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v5_relat_1(sK2,sK1)
    & v5_relat_1(sK2,sK0)
    & v1_relat_1(sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v5_relat_1(X2,X1)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
        & r1_tarski(X0,X1) )
   => ( ? [X2] :
          ( ~ v5_relat_1(X2,sK1)
          & v5_relat_1(X2,sK0)
          & v1_relat_1(X2) )
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ v5_relat_1(X2,sK1)
        & v5_relat_1(X2,sK0)
        & v1_relat_1(X2) )
   => ( ~ v5_relat_1(sK2,sK1)
      & v5_relat_1(sK2,sK0)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v5_relat_1(X2,X1)
          & v5_relat_1(X2,X0)
          & v1_relat_1(X2) )
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ! [X2] :
            ( ( v5_relat_1(X2,X0)
              & v1_relat_1(X2) )
           => v5_relat_1(X2,X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k2_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f24,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f50,plain,(
    ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(global_subsumption,[],[f17,f45])).

fof(f45,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f22,f19])).

fof(f19,plain,(
    ~ v5_relat_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f18,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (21198)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.13/0.41  % (21195)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.41  % (21195)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f55,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(global_subsumption,[],[f18,f17,f54])).
% 0.13/0.41  fof(f54,plain,(
% 0.13/0.41    ~v5_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 0.13/0.41    inference(resolution,[],[f53,f21])).
% 0.13/0.41  fof(f21,plain,(
% 0.13/0.41    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.13/0.41    inference(nnf_transformation,[],[f9])).
% 0.13/0.41  fof(f9,plain,(
% 0.13/0.41    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,axiom,(
% 0.13/0.41    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.13/0.41  fof(f53,plain,(
% 0.13/0.41    ~r1_tarski(k2_relat_1(sK2),sK0)),
% 0.13/0.41    inference(resolution,[],[f50,f33])).
% 0.13/0.41  fof(f33,plain,(
% 0.13/0.41    ( ! [X6] : (r1_tarski(X6,sK1) | ~r1_tarski(X6,sK0)) )),
% 0.13/0.41    inference(superposition,[],[f27,f25])).
% 0.13/0.41  fof(f25,plain,(
% 0.13/0.41    sK1 = k2_xboole_0(sK0,sK1)),
% 0.13/0.41    inference(resolution,[],[f23,f16])).
% 0.13/0.41  fof(f16,plain,(
% 0.13/0.41    r1_tarski(sK0,sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    (~v5_relat_1(sK2,sK1) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2)) & r1_tarski(sK0,sK1)),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13,f12])).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1)) => (? [X2] : (~v5_relat_1(X2,sK1) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) & r1_tarski(sK0,sK1))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ? [X2] : (~v5_relat_1(X2,sK1) & v5_relat_1(X2,sK0) & v1_relat_1(X2)) => (~v5_relat_1(sK2,sK1) & v5_relat_1(sK2,sK0) & v1_relat_1(sK2))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f8,plain,(
% 0.13/0.41    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & v5_relat_1(X2,X0) & v1_relat_1(X2)) & r1_tarski(X0,X1))),
% 0.13/0.41    inference(flattening,[],[f7])).
% 0.13/0.41  fof(f7,plain,(
% 0.13/0.41    ? [X0,X1] : (? [X2] : (~v5_relat_1(X2,X1) & (v5_relat_1(X2,X0) & v1_relat_1(X2))) & r1_tarski(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f6])).
% 0.13/0.41  fof(f6,negated_conjecture,(
% 0.13/0.41    ~! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.13/0.41    inference(negated_conjecture,[],[f5])).
% 0.13/0.41  fof(f5,conjecture,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t218_relat_1)).
% 0.13/0.41  fof(f23,plain,(
% 0.13/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.13/0.41    inference(cnf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f3])).
% 0.13/0.41  fof(f3,axiom,(
% 0.13/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.13/0.41  fof(f27,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r1_tarski(X2,k2_xboole_0(X1,X0)) | ~r1_tarski(X2,X1)) )),
% 0.13/0.41    inference(superposition,[],[f24,f20])).
% 0.13/0.41  fof(f20,plain,(
% 0.13/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.13/0.41  fof(f24,plain,(
% 0.13/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.13/0.41    inference(ennf_transformation,[],[f2])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.13/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.13/0.41  fof(f50,plain,(
% 0.13/0.41    ~r1_tarski(k2_relat_1(sK2),sK1)),
% 0.13/0.41    inference(global_subsumption,[],[f17,f45])).
% 0.13/0.41  fof(f45,plain,(
% 0.13/0.41    ~r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 0.13/0.41    inference(resolution,[],[f22,f19])).
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    ~v5_relat_1(sK2,sK1)),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f22,plain,(
% 0.13/0.41    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.13/0.41    inference(cnf_transformation,[],[f15])).
% 0.13/0.41  fof(f17,plain,(
% 0.13/0.41    v1_relat_1(sK2)),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    v5_relat_1(sK2,sK0)),
% 0.13/0.41    inference(cnf_transformation,[],[f14])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (21195)------------------------------
% 0.13/0.41  % (21195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (21195)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (21195)Memory used [KB]: 6140
% 0.13/0.41  % (21195)Time elapsed: 0.005 s
% 0.13/0.41  % (21195)------------------------------
% 0.13/0.41  % (21195)------------------------------
% 0.13/0.42  % (21190)Success in time 0.061 s
%------------------------------------------------------------------------------
