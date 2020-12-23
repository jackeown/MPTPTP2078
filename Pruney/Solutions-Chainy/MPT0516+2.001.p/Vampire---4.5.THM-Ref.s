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
% DateTime   : Thu Dec  3 12:48:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  40 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 127 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f16,f25,f24,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).

fof(f24,plain,(
    r2_hidden(sK2(k2_relat_1(k8_relat_1(sK0,sK1)),sK0),k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f17,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f17,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f25,plain,(
    ~ r2_hidden(sK2(k2_relat_1(k8_relat_1(sK0,sK1)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:34:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (18846)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (18838)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.48  % (18838)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f16,f25,f24,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    r2_hidden(sK2(k2_relat_1(k8_relat_1(sK0,sK1)),sK0),k2_relat_1(k8_relat_1(sK0,sK1)))),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f17,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(rectify,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),sK0) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),sK0) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f5,plain,(
% 0.22/0.48    ? [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f3])).
% 0.22/0.48  fof(f3,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ~r2_hidden(sK2(k2_relat_1(k8_relat_1(sK0,sK1)),sK0),sK0)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f17,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (18838)------------------------------
% 0.22/0.48  % (18838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (18838)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (18838)Memory used [KB]: 895
% 0.22/0.48  % (18838)Time elapsed: 0.059 s
% 0.22/0.48  % (18838)------------------------------
% 0.22/0.48  % (18838)------------------------------
% 0.22/0.48  % (18833)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (18832)Success in time 0.119 s
%------------------------------------------------------------------------------
