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
% DateTime   : Thu Dec  3 12:48:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  99 expanded)
%              Number of leaves         :    6 (  23 expanded)
%              Depth                    :   15
%              Number of atoms          :  140 ( 372 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f190,plain,(
    $false ),
    inference(subsumption_resolution,[],[f184,f22])).

fof(f22,plain,(
    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK0 != k2_relat_1(k8_relat_1(sK0,sK1))
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

fof(f184,plain,(
    sK0 = k2_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f179,f52])).

fof(f52,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_relat_1(k8_relat_1(X2,sK1)))
      | k2_relat_1(k8_relat_1(X2,sK1)) = X2 ) ),
    inference(resolution,[],[f50,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)
      | r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0) ) ),
    inference(resolution,[],[f40,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X1,sK1)))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK1))) ) ),
    inference(resolution,[],[f26,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | r2_hidden(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f179,plain,(
    r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1)))
    | r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1))) ),
    inference(resolution,[],[f164,f31])).

fof(f164,plain,(
    ! [X1] :
      ( r2_hidden(sK2(sK0,X1),k2_relat_1(k8_relat_1(sK0,sK1)))
      | r1_tarski(sK0,X1) ) ),
    inference(resolution,[],[f161,f21])).

fof(f21,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(sK1))
      | r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X0,sK1)))
      | r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X0,sK1)))
      | ~ r1_tarski(X0,k2_relat_1(sK1))
      | r1_tarski(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f85,f30])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X2,sK1)))
      | ~ r1_tarski(X0,k2_relat_1(sK1))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f81,f30])).

fof(f81,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,X9)
      | r2_hidden(X7,k2_relat_1(k8_relat_1(X8,sK1)))
      | ~ r2_hidden(X7,X8)
      | ~ r1_tarski(X9,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f77,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK1))) ) ),
    inference(resolution,[],[f28,f20])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:50:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (27418)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (27418)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (27419)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.56  % (27426)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f190,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f184,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    sK0 != k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1)) => (sK0 != k2_relat_1(k8_relat_1(sK0,sK1)) & r1_tarski(sK0,k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f7,plain,(
% 0.22/0.56    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.56    inference(flattening,[],[f6])).
% 0.22/0.56  fof(f6,plain,(
% 0.22/0.56    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.56    inference(negated_conjecture,[],[f4])).
% 0.22/0.56  fof(f4,conjecture,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    sK0 = k2_relat_1(k8_relat_1(sK0,sK1))),
% 0.22/0.56    inference(resolution,[],[f179,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X2] : (~r1_tarski(X2,k2_relat_1(k8_relat_1(X2,sK1))) | k2_relat_1(k8_relat_1(X2,sK1)) = X2) )),
% 0.22/0.56    inference(resolution,[],[f50,f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0) | r1_tarski(k2_relat_1(k8_relat_1(X0,sK1)),X0)) )),
% 0.22/0.56    inference(resolution,[],[f40,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X1,sK1))) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f39,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK1)))) )),
% 0.22/0.56    inference(resolution,[],[f26,f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    v1_relat_1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | r2_hidden(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) | (~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) <=> (r2_hidden(X0,k2_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_relat_1)).
% 0.22/0.56  fof(f179,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1)))),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f173])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1))) | r1_tarski(sK0,k2_relat_1(k8_relat_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f164,f31])).
% 0.22/0.56  fof(f164,plain,(
% 0.22/0.56    ( ! [X1] : (r2_hidden(sK2(sK0,X1),k2_relat_1(k8_relat_1(sK0,sK1))) | r1_tarski(sK0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f161,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f11])).
% 0.22/0.56  fof(f161,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(sK1)) | r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X0,sK1))) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f157])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X0,sK1))) | ~r1_tarski(X0,k2_relat_1(sK1)) | r1_tarski(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f85,f30])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | r2_hidden(sK2(X0,X1),k2_relat_1(k8_relat_1(X2,sK1))) | ~r1_tarski(X0,k2_relat_1(sK1)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(resolution,[],[f81,f30])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    ( ! [X8,X7,X9] : (~r2_hidden(X7,X9) | r2_hidden(X7,k2_relat_1(k8_relat_1(X8,sK1))) | ~r2_hidden(X7,X8) | ~r1_tarski(X9,k2_relat_1(sK1))) )),
% 0.22/0.56    inference(resolution,[],[f77,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_relat_1(sK1)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,sK1)))) )),
% 0.22/0.56    inference(resolution,[],[f28,f20])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k2_relat_1(X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (27418)------------------------------
% 0.22/0.56  % (27418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (27418)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (27418)Memory used [KB]: 6268
% 0.22/0.56  % (27418)Time elapsed: 0.115 s
% 0.22/0.56  % (27418)------------------------------
% 0.22/0.56  % (27418)------------------------------
% 0.22/0.56  % (27436)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (27412)Success in time 0.195 s
%------------------------------------------------------------------------------
