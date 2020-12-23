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
% DateTime   : Thu Dec  3 12:48:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  75 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 428 expanded)
%              Number of equality atoms :   19 (  33 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(subsumption_resolution,[],[f181,f39])).

fof(f39,plain,(
    sK1 != k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(superposition,[],[f24,f38])).

fof(f38,plain,(
    ! [X0] : k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != k2_relat_1(k8_relat_1(sK1,sK2))
    & r1_tarski(sK1,k2_relat_1(sK2))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k2_relat_1(k8_relat_1(X0,X1)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( sK1 != k2_relat_1(k8_relat_1(sK1,sK2))
      & r1_tarski(sK1,k2_relat_1(sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f24,plain,(
    sK1 != k2_relat_1(k8_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f181,plain,(
    sK1 = k3_xboole_0(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f156,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f156,plain,(
    sP0(sK1,k2_relat_1(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( sP0(sK1,k2_relat_1(sK2),sK1)
    | sP0(sK1,k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f140,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0,sK1),k2_relat_1(sK2))
      | sP0(sK1,X0,sK1) ) ),
    inference(resolution,[],[f72,f23])).

fof(f23,plain,(
    r1_tarski(sK1,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X14,X12,X13] :
      ( ~ r1_tarski(X12,X14)
      | r2_hidden(sK3(X12,X13,X12),X14)
      | sP0(X12,X13,X12) ) ),
    inference(resolution,[],[f68,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | sP0(X0,X1,X0) ) ),
    inference(factoring,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X0)
              & r2_hidden(sK3(X0,X1,X2),X1) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X0)
            & r2_hidden(sK3(X0,X1,X2),X1) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X0),X1)
      | sP0(X0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f139,f68])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X0),X0)
      | ~ r2_hidden(sK3(X0,X1,X0),X1)
      | sP0(X0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X0),X0)
      | ~ r2_hidden(sK3(X0,X1,X0),X1)
      | sP0(X0,X1,X0)
      | sP0(X0,X1,X0) ) ),
    inference(resolution,[],[f33,f68])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:29:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (7179)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.45  % (7179)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (7197)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.47  % (7189)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f182,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f181,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    sK1 != k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.22/0.48    inference(superposition,[],[f24,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (k2_relat_1(k8_relat_1(X0,sK2)) = k3_xboole_0(k2_relat_1(sK2),X0)) )),
% 0.22/0.48    inference(resolution,[],[f26,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    sK1 != k2_relat_1(k8_relat_1(sK1,sK2)) & r1_tarski(sK1,k2_relat_1(sK2)) & v1_relat_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1)) => (sK1 != k2_relat_1(k8_relat_1(sK1,sK2)) & r1_tarski(sK1,k2_relat_1(sK2)) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1] : ((k2_relat_1(k8_relat_1(X0,X1)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k2_relat_1(X1)) => k2_relat_1(k8_relat_1(X0,X1)) = X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    sK1 != k2_relat_1(k8_relat_1(sK1,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f181,plain,(
% 0.22/0.48    sK1 = k3_xboole_0(k2_relat_1(sK2),sK1)),
% 0.22/0.48    inference(resolution,[],[f156,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.48    inference(definition_folding,[],[f2,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    sP0(sK1,k2_relat_1(sK2),sK1)),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f151])).
% 0.22/0.48  fof(f151,plain,(
% 0.22/0.48    sP0(sK1,k2_relat_1(sK2),sK1) | sP0(sK1,k2_relat_1(sK2),sK1)),
% 0.22/0.48    inference(resolution,[],[f140,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X0] : (r2_hidden(sK3(sK1,X0,sK1),k2_relat_1(sK2)) | sP0(sK1,X0,sK1)) )),
% 0.22/0.48    inference(resolution,[],[f72,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    r1_tarski(sK1,k2_relat_1(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X14,X12,X13] : (~r1_tarski(X12,X14) | r2_hidden(sK3(X12,X13,X12),X14) | sP0(X12,X13,X12)) )),
% 0.22/0.48    inference(resolution,[],[f68,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | sP0(X0,X1,X0)) )),
% 0.22/0.48    inference(factoring,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X0) & r2_hidden(sK3(X0,X1,X2),X1)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.48    inference(rectify,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.48    inference(flattening,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.48    inference(nnf_transformation,[],[f12])).
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X0),X1) | sP0(X0,X1,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f139,f68])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X0),X0) | ~r2_hidden(sK3(X0,X1,X0),X1) | sP0(X0,X1,X0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1,X0),X0) | ~r2_hidden(sK3(X0,X1,X0),X1) | sP0(X0,X1,X0) | sP0(X0,X1,X0)) )),
% 0.22/0.48    inference(resolution,[],[f33,f68])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7179)------------------------------
% 0.22/0.48  % (7179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7179)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7179)Memory used [KB]: 6396
% 0.22/0.48  % (7179)Time elapsed: 0.063 s
% 0.22/0.48  % (7179)------------------------------
% 0.22/0.48  % (7179)------------------------------
% 0.22/0.49  % (7169)Success in time 0.124 s
%------------------------------------------------------------------------------
