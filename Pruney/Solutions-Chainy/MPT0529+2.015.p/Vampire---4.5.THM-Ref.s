%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  71 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   15
%              Number of atoms          :  119 ( 239 expanded)
%              Number of equality atoms :   13 (  34 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f127,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f126,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f126,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f123,f24])).

fof(f24,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f123,plain,
    ( k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f122,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f122,plain,(
    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f116,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f116,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_relat_1(k8_relat_1(sK0,sK2)),X0),sK1)
      | r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),X0) ) ),
    inference(resolution,[],[f59,f23])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,X3)
      | r2_hidden(sK3(k2_relat_1(k8_relat_1(X1,sK2)),X2),X3)
      | r1_tarski(k2_relat_1(k8_relat_1(X1,sK2)),X2) ) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k2_relat_1(k8_relat_1(X0,sK2)),X1),X0)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1) ) ),
    inference(resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK2)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (1057)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.46  % (1057)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (1066)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f127,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    v1_relat_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    ~v1_relat_1(sK2)),
% 0.20/0.48    inference(resolution,[],[f126,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.48    inference(subsumption_resolution,[],[f123,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    k8_relat_1(sK0,sK2) = k8_relat_1(sK1,k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.20/0.48    inference(resolution,[],[f122,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1 | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(flattening,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)),
% 0.20/0.48    inference(resolution,[],[f116,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(k2_relat_1(k8_relat_1(sK0,sK2)),X0),sK1) | r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),X0)) )),
% 0.20/0.48    inference(resolution,[],[f59,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    r1_tarski(sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X2,X3,X1] : (~r1_tarski(X1,X3) | r2_hidden(sK3(k2_relat_1(k8_relat_1(X1,sK2)),X2),X3) | r1_tarski(k2_relat_1(k8_relat_1(X1,sK2)),X2)) )),
% 0.20/0.48    inference(resolution,[],[f42,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(k2_relat_1(k8_relat_1(X0,sK2)),X1),X0) | r1_tarski(k2_relat_1(k8_relat_1(X0,sK2)),X1)) )),
% 0.20/0.48    inference(resolution,[],[f40,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK2))) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f30,f22])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (1057)------------------------------
% 0.20/0.48  % (1057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1057)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (1057)Memory used [KB]: 6268
% 0.20/0.48  % (1057)Time elapsed: 0.074 s
% 0.20/0.48  % (1057)------------------------------
% 0.20/0.48  % (1057)------------------------------
% 0.20/0.48  % (1074)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.48  % (1047)Success in time 0.13 s
%------------------------------------------------------------------------------
