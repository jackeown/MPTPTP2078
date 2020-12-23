%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  62 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 266 expanded)
%              Number of equality atoms :   82 ( 178 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f52,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51,f18])).

fof(f18,plain,(
    sK1 != sK4 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( sK1 != sK4
    & sK1 != sK3
    & k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f5,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) )
   => ( sK1 != sK4
      & sK1 != sK3
      & k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(f51,plain,(
    sK1 = sK4 ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f17,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,
    ( sK1 = sK3
    | sK1 = sK4 ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ! [X4,X2,X0] :
      ( ~ sP0(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK5(X0,X1,X2) != X0
              & sK5(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X0
            | sK5(X0,X1,X2) = X1
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X0
            & sK5(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X0
          | sK5(X0,X1,X2) = X1
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f33,plain,(
    ! [X0,X1] : sP0(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f26,f19])).

fof(f19,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f6])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
      | sK3 = X0
      | sK4 = X0 ) ),
    inference(resolution,[],[f41,f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
    sP0(sK4,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(superposition,[],[f33,f28])).

fof(f28,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4) ),
    inference(definition_unfolding,[],[f16,f19,f19])).

fof(f16,plain,(
    k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (8743)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (8738)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (8754)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.51  % (8744)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (8744)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f51,f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    sK1 != sK4),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,plain,(
% 0.22/0.51    sK1 != sK4 & sK1 != sK3 & k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f5,f8])).
% 0.22/0.51  fof(f8,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3)) => (sK1 != sK4 & sK1 != sK3 & k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f5,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.22/0.51    inference(negated_conjecture,[],[f3])).
% 0.22/0.51  fof(f3,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_zfmisc_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    sK1 = sK4),
% 0.22/0.51    inference(subsumption_resolution,[],[f47,f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    sK1 != sK3),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    sK1 = sK3 | sK1 = sK4),
% 0.22/0.51    inference(resolution,[],[f44,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(resolution,[],[f33,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X4,X2,X0] : (~sP0(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.51    inference(equality_resolution,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f12,f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.51    inference(rectify,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.51    inference(nnf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,plain,(
% 0.22/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0,X1] : (sP0(X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 0.22/0.51    inference(definition_unfolding,[],[f26,f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_enumset1)).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.51    inference(nnf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.51    inference(definition_folding,[],[f1,f6])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | sK3 = X0 | sK4 = X0) )),
% 0.22/0.51    inference(resolution,[],[f41,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    sP0(sK4,sK3,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 0.22/0.51    inference(superposition,[],[f33,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)),
% 0.22/0.51    inference(definition_unfolding,[],[f16,f19,f19])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    k2_tarski(sK1,sK2) = k2_tarski(sK3,sK4)),
% 0.22/0.51    inference(cnf_transformation,[],[f9])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (8744)------------------------------
% 0.22/0.51  % (8744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8744)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (8744)Memory used [KB]: 10746
% 0.22/0.51  % (8744)Time elapsed: 0.110 s
% 0.22/0.51  % (8744)------------------------------
% 0.22/0.51  % (8744)------------------------------
% 0.22/0.51  % (8767)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (8767)Refutation not found, incomplete strategy% (8767)------------------------------
% 0.22/0.51  % (8767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8767)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8767)Memory used [KB]: 1663
% 0.22/0.51  % (8767)Time elapsed: 0.001 s
% 0.22/0.51  % (8767)------------------------------
% 0.22/0.51  % (8767)------------------------------
% 0.22/0.52  % (8737)Success in time 0.158 s
%------------------------------------------------------------------------------
