%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  84 expanded)
%              Number of leaves         :    8 (  21 expanded)
%              Depth                    :   17
%              Number of atoms          :  141 ( 318 expanded)
%              Number of equality atoms :   29 (  89 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

% (2267)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f15,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    & r1_tarski(sK0,k1_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X1,X0)
        & r1_tarski(X0,k1_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k9_relat_1(sK1,sK0)
      & r1_tarski(sK0,k1_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f61,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f60,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f60,plain,(
    ! [X0] : r1_tarski(sK0,k4_xboole_0(X0,sK0)) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f25,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k1_relat_1(sK1))
      | r1_tarski(sK0,k4_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f57,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(X0,sK0)),X1)
      | ~ r1_tarski(X1,k1_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f55,f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(X0,sK0)),X1)
      | ~ r1_tarski(X1,k1_relat_1(sK1))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0,X0)
      | ~ r2_hidden(sK3(sK0,X0),X1)
      | ~ r1_tarski(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(sK0,X2),k1_relat_1(sK1))
      | r1_tarski(sK0,X2) ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(trivial_inequality_removal,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,k1_relat_1(sK1)) ) ),
    inference(superposition,[],[f40,f26])).

fof(f26,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f39,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_relat_1(sK1),X0)
      | k1_xboole_0 != k9_relat_1(sK1,X0) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

% (2260)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (2240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.48  % (2240)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % (2267)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k9_relat_1(sK1,sK0) & r1_tarski(sK0,k1_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    k1_xboole_0 = sK0),
% 0.21/0.48    inference(resolution,[],[f60,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(sK0,k4_xboole_0(X0,sK0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(sK0,k1_relat_1(sK1)) | r1_tarski(sK0,k4_xboole_0(X0,sK0))) )),
% 0.21/0.48    inference(resolution,[],[f57,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,k4_xboole_0(X0,sK0)),X1) | ~r1_tarski(X1,k1_relat_1(sK1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f24])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(sK0,k4_xboole_0(X0,sK0)),X1) | ~r1_tarski(X1,k1_relat_1(sK1)) | k1_xboole_0 = sK0) )),
% 0.21/0.48    inference(resolution,[],[f49,f32])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(sK0,X0) | ~r2_hidden(sK3(sK0,X0),X1) | ~r1_tarski(X1,k1_relat_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f45,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2] : (~r2_hidden(sK3(sK0,X2),k1_relat_1(sK1)) | r1_tarski(sK0,X2)) )),
% 0.21/0.48    inference(resolution,[],[f42,f34])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,k1_relat_1(sK1))) )),
% 0.21/0.48    inference(superposition,[],[f40,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(sK1,X0) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_relat_1(sK1))) )),
% 0.21/0.48    inference(resolution,[],[f39,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(k1_relat_1(sK1),X0) | k1_xboole_0 != k9_relat_1(sK1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f30,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.49  % (2260)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (2240)------------------------------
% 0.21/0.49  % (2240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2240)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (2240)Memory used [KB]: 10746
% 0.21/0.49  % (2240)Time elapsed: 0.091 s
% 0.21/0.49  % (2240)------------------------------
% 0.21/0.49  % (2240)------------------------------
% 0.21/0.49  % (2236)Success in time 0.127 s
%------------------------------------------------------------------------------
