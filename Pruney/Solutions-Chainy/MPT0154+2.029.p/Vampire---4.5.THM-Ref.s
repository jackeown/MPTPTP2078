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
% DateTime   : Thu Dec  3 12:33:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 106 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   17
%              Number of atoms          :  259 ( 681 expanded)
%              Number of equality atoms :  161 ( 452 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(resolution,[],[f136,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f6,f7])).

fof(f7,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f6,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f136,plain,(
    ! [X2] : ~ sP0(sK2,sK1,sK1,X2) ),
    inference(subsumption_resolution,[],[f132,f45])).

fof(f45,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X0,X5,X2,X3) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f132,plain,(
    ! [X2] :
      ( ~ sP0(sK2,sK1,sK1,X2)
      | ~ r2_hidden(sK1,X2) ) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,(
    ! [X2] :
      ( sK1 != sK1
      | ~ sP0(sK2,sK1,sK1,X2)
      | ~ r2_hidden(sK1,X2) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X2] :
      ( sK1 != sK1
      | ~ sP0(sK2,sK1,sK1,X2)
      | ~ r2_hidden(sK1,X2)
      | ~ sP0(sK2,sK1,sK1,X2) ) ),
    inference(superposition,[],[f58,f103])).

fof(f103,plain,(
    ! [X0] :
      ( sK1 = sK3(sK1,sK2,X0)
      | ~ sP0(sK2,sK1,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f102,f44])).

fof(f44,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f102,plain,(
    ! [X0] :
      ( ~ sP0(sK2,sK1,sK1,X0)
      | ~ r2_hidden(sK2,X0)
      | sK1 = sK3(sK1,sK2,X0) ) ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,(
    ! [X0] :
      ( sK2 != sK2
      | ~ sP0(sK2,sK1,sK1,X0)
      | ~ r2_hidden(sK2,X0)
      | sK1 = sK3(sK1,sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( sK2 != sK2
      | ~ sP0(sK2,sK1,sK1,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ sP0(sK2,sK1,sK1,X0)
      | sK1 = sK3(sK1,sK2,X0) ) ),
    inference(superposition,[],[f59,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sK2 = sK3(sK1,sK2,X0)
      | ~ sP0(sK2,sK1,sK1,X0)
      | sK1 = sK3(sK1,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f57,f29])).

fof(f29,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X0 = X5
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X0] :
      ( ~ sP0(sK2,sK1,sK1,X0)
      | sK2 = sK3(sK1,sK2,X0)
      | sK1 = sK3(sK1,sK2,X0)
      | r2_hidden(sK3(sK1,sK2,X0),X0) ) ),
    inference(superposition,[],[f52,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) = X1
      | sK3(X0,X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f52,plain,(
    ~ sP0(sK2,sK1,sK1,k2_tarski(sK1,sK2)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( k2_tarski(sK1,sK2) != X0
      | ~ sP0(sK2,sK1,sK1,X0) ) ),
    inference(superposition,[],[f22,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | ~ sP0(X2,X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f22,plain,(
    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f9])).

fof(f9,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X2] :
      ( sK2 != sK3(sK1,sK2,X2)
      | ~ sP0(sK2,sK1,sK1,X2)
      | ~ r2_hidden(sK3(sK1,sK2,X2),X2) ) ),
    inference(superposition,[],[f52,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) != X1
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ! [X1] :
      ( sK1 != sK3(sK1,sK2,X1)
      | ~ sP0(sK2,sK1,sK1,X1)
      | ~ r2_hidden(sK3(sK1,sK2,X1),X1) ) ),
    inference(superposition,[],[f52,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) != X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:35:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (1180)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.46  % (1188)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.46  % (1188)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f193,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(resolution,[],[f136,f47])).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.19/0.47    inference(equality_resolution,[],[f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.47    inference(nnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.19/0.47    inference(definition_folding,[],[f6,f7])).
% 0.19/0.47  fof(f7,plain,(
% 0.19/0.47    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.19/0.47  fof(f6,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.47    inference(ennf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.19/0.47  fof(f136,plain,(
% 0.19/0.47    ( ! [X2] : (~sP0(sK2,sK1,sK1,X2)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f132,f45])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | ~sP0(X0,X5,X2,X3)) )),
% 0.19/0.47    inference(equality_resolution,[],[f31])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.19/0.47    inference(rectify,[],[f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.19/0.47    inference(flattening,[],[f16])).
% 0.19/0.47  fof(f16,plain,(
% 0.19/0.47    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.19/0.47    inference(nnf_transformation,[],[f7])).
% 0.19/0.47  fof(f132,plain,(
% 0.19/0.47    ( ! [X2] : (~sP0(sK2,sK1,sK1,X2) | ~r2_hidden(sK1,X2)) )),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f131])).
% 0.19/0.47  fof(f131,plain,(
% 0.19/0.47    ( ! [X2] : (sK1 != sK1 | ~sP0(sK2,sK1,sK1,X2) | ~r2_hidden(sK1,X2)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f119])).
% 0.19/0.47  fof(f119,plain,(
% 0.19/0.47    ( ! [X2] : (sK1 != sK1 | ~sP0(sK2,sK1,sK1,X2) | ~r2_hidden(sK1,X2) | ~sP0(sK2,sK1,sK1,X2)) )),
% 0.19/0.47    inference(superposition,[],[f58,f103])).
% 0.19/0.47  fof(f103,plain,(
% 0.19/0.47    ( ! [X0] : (sK1 = sK3(sK1,sK2,X0) | ~sP0(sK2,sK1,sK1,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f102,f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X1,X2,X3)) )),
% 0.19/0.47    inference(equality_resolution,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f102,plain,(
% 0.19/0.47    ( ! [X0] : (~sP0(sK2,sK1,sK1,X0) | ~r2_hidden(sK2,X0) | sK1 = sK3(sK1,sK2,X0)) )),
% 0.19/0.47    inference(trivial_inequality_removal,[],[f101])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    ( ! [X0] : (sK2 != sK2 | ~sP0(sK2,sK1,sK1,X0) | ~r2_hidden(sK2,X0) | sK1 = sK3(sK1,sK2,X0)) )),
% 0.19/0.47    inference(duplicate_literal_removal,[],[f86])).
% 0.19/0.47  fof(f86,plain,(
% 0.19/0.47    ( ! [X0] : (sK2 != sK2 | ~sP0(sK2,sK1,sK1,X0) | ~r2_hidden(sK2,X0) | ~sP0(sK2,sK1,sK1,X0) | sK1 = sK3(sK1,sK2,X0)) )),
% 0.19/0.47    inference(superposition,[],[f59,f62])).
% 0.19/0.47  fof(f62,plain,(
% 0.19/0.47    ( ! [X0] : (sK2 = sK3(sK1,sK2,X0) | ~sP0(sK2,sK1,sK1,X0) | sK1 = sK3(sK1,sK2,X0)) )),
% 0.19/0.47    inference(subsumption_resolution,[],[f57,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ( ! [X2,X0,X5,X3,X1] : (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | ~sP0(X0,X1,X2,X3)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ( ! [X0] : (~sP0(sK2,sK1,sK1,X0) | sK2 = sK3(sK1,sK2,X0) | sK1 = sK3(sK1,sK2,X0) | r2_hidden(sK3(sK1,sK2,X0),X0)) )),
% 0.19/0.47    inference(superposition,[],[f52,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f14])).
% 0.19/0.47  fof(f14,plain,(
% 0.19/0.47    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f13,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.47    inference(rectify,[],[f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.47    inference(flattening,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.19/0.47    inference(nnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ~sP0(sK2,sK1,sK1,k2_tarski(sK1,sK2))),
% 0.19/0.47    inference(equality_resolution,[],[f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ( ! [X0] : (k2_tarski(sK1,sK2) != X0 | ~sP0(sK2,sK1,sK1,X0)) )),
% 0.19/0.47    inference(superposition,[],[f22,f38])).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2)),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f5,f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK1,sK2) != k1_enumset1(sK1,sK1,sK2)),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f5,plain,(
% 0.19/0.47    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.47    inference(negated_conjecture,[],[f3])).
% 0.19/0.47  fof(f3,conjecture,(
% 0.19/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.47  fof(f59,plain,(
% 0.19/0.47    ( ! [X2] : (sK2 != sK3(sK1,sK2,X2) | ~sP0(sK2,sK1,sK1,X2) | ~r2_hidden(sK3(sK1,sK2,X2),X2)) )),
% 0.19/0.47    inference(superposition,[],[f52,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    ( ! [X1] : (sK1 != sK3(sK1,sK2,X1) | ~sP0(sK2,sK1,sK1,X1) | ~r2_hidden(sK3(sK1,sK2,X1),X1)) )),
% 0.19/0.47    inference(superposition,[],[f52,f27])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X0 | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f15])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (1188)------------------------------
% 0.19/0.47  % (1188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (1188)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (1188)Memory used [KB]: 1663
% 0.19/0.47  % (1188)Time elapsed: 0.060 s
% 0.19/0.47  % (1188)------------------------------
% 0.19/0.47  % (1188)------------------------------
% 0.19/0.48  % (1169)Success in time 0.125 s
%------------------------------------------------------------------------------
