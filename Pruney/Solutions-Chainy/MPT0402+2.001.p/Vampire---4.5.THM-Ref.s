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
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 104 expanded)
%              Number of leaves         :    9 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 ( 470 expanded)
%              Number of equality atoms :   92 (  95 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(subsumption_resolution,[],[f80,f24])).

fof(f24,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK4,sK2)
    & ~ r1_tarski(sK4,sK1)
    & r2_hidden(sK4,sK3)
    & r1_setfam_1(sK3,k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) )
        & r1_setfam_1(X2,k2_tarski(X0,X1)) )
   => ( ? [X3] :
          ( ~ r1_tarski(X3,sK2)
          & ~ r1_tarski(X3,sK1)
          & r2_hidden(X3,sK3) )
      & r1_setfam_1(sK3,k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X3] :
        ( ~ r1_tarski(X3,sK2)
        & ~ r1_tarski(X3,sK1)
        & r2_hidden(X3,sK3) )
   => ( ~ r1_tarski(sK4,sK2)
      & ~ r1_tarski(sK4,sK1)
      & r2_hidden(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
      & r1_setfam_1(X2,k2_tarski(X0,X1)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_setfam_1(X2,k2_tarski(X0,X1))
       => ! [X3] :
            ~ ( ~ r1_tarski(X3,X1)
              & ~ r1_tarski(X3,X0)
              & r2_hidden(X3,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X2,k2_tarski(X0,X1))
     => ! [X3] :
          ~ ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_setfam_1)).

fof(f80,plain,(
    ~ r2_hidden(sK4,sK3) ),
    inference(subsumption_resolution,[],[f79,f25])).

fof(f25,plain,(
    ~ r1_tarski(sK4,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( r1_tarski(sK4,sK1)
    | ~ r2_hidden(sK4,sK3) ),
    inference(superposition,[],[f58,f77])).

fof(f77,plain,(
    sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(subsumption_resolution,[],[f76,f24])).

fof(f76,plain,
    ( ~ r2_hidden(sK4,sK3)
    | sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(subsumption_resolution,[],[f74,f26])).

fof(f26,plain,(
    ~ r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,
    ( r1_tarski(sK4,sK2)
    | ~ r2_hidden(sK4,sK3)
    | sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(superposition,[],[f58,f72])).

fof(f72,plain,
    ( sK2 = sK5(k2_tarski(sK1,sK2),sK4)
    | sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(resolution,[],[f66,f24])).

fof(f66,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | sK2 = sK5(k2_tarski(sK1,sK2),X4)
      | sK1 = sK5(k2_tarski(sK1,sK2),X4) ) ),
    inference(resolution,[],[f63,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k2_tarski(sK1,sK2),X0),k2_tarski(sK1,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f28,f23])).

fof(f23,plain,(
    r1_setfam_1(sK3,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK5(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK5(X1,X2))
            & r2_hidden(sK5(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f8,f15])).

fof(f15,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK5(X1,X2))
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f63,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,k2_tarski(X4,X6))
      | X4 = X5
      | X5 = X6 ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X6,X4,X5] :
      ( X4 = X5
      | X4 = X5
      | ~ r2_hidden(X5,k2_tarski(X4,X6))
      | X5 = X6 ) ),
    inference(resolution,[],[f30,f50])).

fof(f50,plain,(
    ! [X0,X1] : sP0(X1,X0,X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f43,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f9,f10])).

fof(f10,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | X1 = X5
      | X2 = X5
      | ~ r2_hidden(X5,X3)
      | X0 = X5 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK6(X0,X1,X2,X3) != X0
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X0
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X2
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f20])).

fof(f20,plain,(
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
     => ( ( ( sK6(X0,X1,X2,X3) != X0
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X0
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X2
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(nnf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK5(k2_tarski(sK1,sK2),X0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f29,f23])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK5(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (17556)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.48  % (17556)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (17564)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    r2_hidden(sK4,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    (~r1_tarski(sK4,sK2) & ~r1_tarski(sK4,sK1) & r2_hidden(sK4,sK3)) & r1_setfam_1(sK3,k2_tarski(sK1,sK2))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f7,f13,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)) & r1_setfam_1(X2,k2_tarski(X0,X1))) => (? [X3] : (~r1_tarski(X3,sK2) & ~r1_tarski(X3,sK1) & r2_hidden(X3,sK3)) & r1_setfam_1(sK3,k2_tarski(sK1,sK2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X3] : (~r1_tarski(X3,sK2) & ~r1_tarski(X3,sK1) & r2_hidden(X3,sK3)) => (~r1_tarski(sK4,sK2) & ~r1_tarski(sK4,sK1) & r2_hidden(sK4,sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)) & r1_setfam_1(X2,k2_tarski(X0,X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (r1_setfam_1(X2,k2_tarski(X0,X1)) => ! [X3] : ~(~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_setfam_1(X2,k2_tarski(X0,X1)) => ! [X3] : ~(~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_setfam_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ~r2_hidden(sK4,sK3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~r1_tarski(sK4,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    r1_tarski(sK4,sK1) | ~r2_hidden(sK4,sK3)),
% 0.21/0.48    inference(superposition,[],[f58,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f76,f24])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ~r2_hidden(sK4,sK3) | sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~r1_tarski(sK4,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    r1_tarski(sK4,sK2) | ~r2_hidden(sK4,sK3) | sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.21/0.48    inference(superposition,[],[f58,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    sK2 = sK5(k2_tarski(sK1,sK2),sK4) | sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.21/0.48    inference(resolution,[],[f66,f24])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,sK3) | sK2 = sK5(k2_tarski(sK1,sK2),X4) | sK1 = sK5(k2_tarski(sK1,sK2),X4)) )),
% 0.21/0.48    inference(resolution,[],[f63,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK5(k2_tarski(sK1,sK2),X0),k2_tarski(sK1,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.48    inference(resolution,[],[f28,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    r1_setfam_1(sK3,k2_tarski(sK1,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK5(X1,X2),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,sK5(X1,X2)) & r2_hidden(sK5(X1,X2),X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f8,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X2,X1] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) => (r1_tarski(X2,sK5(X1,X2)) & r2_hidden(sK5(X1,X2),X1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (~r2_hidden(X5,k2_tarski(X4,X6)) | X4 = X5 | X5 = X6) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X6,X4,X5] : (X4 = X5 | X4 = X5 | ~r2_hidden(X5,k2_tarski(X4,X6)) | X5 = X6) )),
% 0.21/0.48    inference(resolution,[],[f30,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sP0(X1,X0,X0,k2_tarski(X0,X1))) )),
% 0.21/0.48    inference(superposition,[],[f43,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.48    inference(nnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.21/0.48    inference(definition_folding,[],[f9,f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X3,X1] : (~sP0(X0,X1,X2,X3) | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3) | X0 = X5) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK6(X0,X1,X2,X3) != X0 & sK6(X0,X1,X2,X3) != X1 & sK6(X0,X1,X2,X3) != X2) | ~r2_hidden(sK6(X0,X1,X2,X3),X3)) & (sK6(X0,X1,X2,X3) = X0 | sK6(X0,X1,X2,X3) = X1 | sK6(X0,X1,X2,X3) = X2 | r2_hidden(sK6(X0,X1,X2,X3),X3))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.48    inference(rectify,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(X0,sK5(k2_tarski(sK1,sK2),X0)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.48    inference(resolution,[],[f29,f23])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,sK5(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17556)------------------------------
% 0.21/0.48  % (17556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17556)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17556)Memory used [KB]: 6268
% 0.21/0.48  % (17556)Time elapsed: 0.068 s
% 0.21/0.48  % (17556)------------------------------
% 0.21/0.48  % (17556)------------------------------
% 0.21/0.49  % (17548)Success in time 0.125 s
%------------------------------------------------------------------------------
