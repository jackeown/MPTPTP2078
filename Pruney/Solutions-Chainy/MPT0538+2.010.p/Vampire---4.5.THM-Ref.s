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
% DateTime   : Thu Dec  3 12:49:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  40 expanded)
%              Number of leaves         :   10 (  11 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 (  85 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(subsumption_resolution,[],[f41,f26])).

fof(f26,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f40,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f38,f26])).

fof(f38,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f37,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f37,plain,
    ( ~ v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f35,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f35,plain,
    ( r2_hidden(sK1(k2_relat_1(k1_xboole_0),sK0),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f34,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f24,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)
   => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (31770)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (31794)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.57  % (31770)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (31773)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (31778)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f41,f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f40,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f38,f26])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ~v1_relat_1(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f37,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ~v1_xboole_0(k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f35,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(rectify,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    r2_hidden(sK1(k2_relat_1(k1_xboole_0),sK0),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f34,f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.57    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f24,f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(flattening,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0) => k1_xboole_0 != k8_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f10,plain,(
% 0.21/0.57    ? [X0] : k1_xboole_0 != k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,negated_conjecture,(
% 0.21/0.57    ~! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.57    inference(negated_conjecture,[],[f7])).
% 0.21/0.57  fof(f7,conjecture,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (31770)------------------------------
% 0.21/0.57  % (31770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (31770)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (31770)Memory used [KB]: 1663
% 0.21/0.57  % (31770)Time elapsed: 0.125 s
% 0.21/0.57  % (31770)------------------------------
% 0.21/0.57  % (31770)------------------------------
% 0.21/0.58  % (31769)Success in time 0.209 s
%------------------------------------------------------------------------------
