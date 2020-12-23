%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   40 (  99 expanded)
%              Number of leaves         :    8 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  171 ( 434 expanded)
%              Number of equality atoms :   60 (  62 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f22,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(sK4,sK2)
    & ~ r1_tarski(sK4,sK1)
    & r2_hidden(sK4,sK3)
    & r1_setfam_1(sK3,k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f6,f11,f10])).

fof(f10,plain,
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

fof(f11,plain,
    ( ? [X3] :
        ( ~ r1_tarski(X3,sK2)
        & ~ r1_tarski(X3,sK1)
        & r2_hidden(X3,sK3) )
   => ( ~ r1_tarski(sK4,sK2)
      & ~ r1_tarski(sK4,sK1)
      & r2_hidden(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X1)
          & ~ r1_tarski(X3,X0)
          & r2_hidden(X3,X2) )
      & r1_setfam_1(X2,k2_tarski(X0,X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_setfam_1(X2,k2_tarski(X0,X1))
       => ! [X3] :
            ~ ( ~ r1_tarski(X3,X1)
              & ~ r1_tarski(X3,X0)
              & r2_hidden(X3,X2) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_setfam_1(X2,k2_tarski(X0,X1))
     => ! [X3] :
          ~ ( ~ r1_tarski(X3,X1)
            & ~ r1_tarski(X3,X0)
            & r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_setfam_1)).

fof(f57,plain,(
    ~ r2_hidden(sK4,sK3) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f23,plain,(
    ~ r1_tarski(sK4,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f56,plain,
    ( r1_tarski(sK4,sK1)
    | ~ r2_hidden(sK4,sK3) ),
    inference(superposition,[],[f44,f54])).

fof(f54,plain,(
    sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(subsumption_resolution,[],[f53,f22])).

fof(f53,plain,
    ( ~ r2_hidden(sK4,sK3)
    | sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(subsumption_resolution,[],[f51,f24])).

fof(f24,plain,(
    ~ r1_tarski(sK4,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,
    ( r1_tarski(sK4,sK2)
    | ~ r2_hidden(sK4,sK3)
    | sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(superposition,[],[f44,f49])).

fof(f49,plain,
    ( sK2 = sK5(k2_tarski(sK1,sK2),sK4)
    | sK1 = sK5(k2_tarski(sK1,sK2),sK4) ),
    inference(resolution,[],[f48,f22])).

fof(f48,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK3)
      | sK2 = sK5(k2_tarski(sK1,sK2),X4)
      | sK1 = sK5(k2_tarski(sK1,sK2),X4) ) ),
    inference(resolution,[],[f45,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k2_tarski(sK1,sK2),X0),k2_tarski(sK1,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    r1_setfam_1(sK3,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK5(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X2,sK5(X1,X2))
            & r2_hidden(sK5(X1,X2),X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f13])).

fof(f13,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( r1_tarski(X2,X3)
          & r2_hidden(X3,X1) )
     => ( r1_tarski(X2,sK5(X1,X2))
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f8])).

fof(f8,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK6(X0,X1,X2) != X0
              & sK6(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X0
            | sK6(X0,X1,X2) = X1
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X0
            & sK6(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X0
          | sK6(X0,X1,X2) = X1
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK5(k2_tarski(sK1,sK2),X0))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f26,f21])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK5(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:53:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.54  % (24779)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.55  % (24782)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.55  % (24785)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.55  % (24787)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.56  % (24779)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f57,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    r2_hidden(sK4,sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    (~r1_tarski(sK4,sK2) & ~r1_tarski(sK4,sK1) & r2_hidden(sK4,sK3)) & r1_setfam_1(sK3,k2_tarski(sK1,sK2))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f6,f11,f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)) & r1_setfam_1(X2,k2_tarski(X0,X1))) => (? [X3] : (~r1_tarski(X3,sK2) & ~r1_tarski(X3,sK1) & r2_hidden(X3,sK3)) & r1_setfam_1(sK3,k2_tarski(sK1,sK2)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ? [X3] : (~r1_tarski(X3,sK2) & ~r1_tarski(X3,sK1) & r2_hidden(X3,sK3)) => (~r1_tarski(sK4,sK2) & ~r1_tarski(sK4,sK1) & r2_hidden(sK4,sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f6,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)) & r1_setfam_1(X2,k2_tarski(X0,X1)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : (r1_setfam_1(X2,k2_tarski(X0,X1)) => ! [X3] : ~(~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)))),
% 0.22/0.56    inference(negated_conjecture,[],[f3])).
% 0.22/0.56  fof(f3,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : (r1_setfam_1(X2,k2_tarski(X0,X1)) => ! [X3] : ~(~r1_tarski(X3,X1) & ~r1_tarski(X3,X0) & r2_hidden(X3,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_setfam_1)).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ~r2_hidden(sK4,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f56,f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ~r1_tarski(sK4,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    r1_tarski(sK4,sK1) | ~r2_hidden(sK4,sK3)),
% 0.22/0.56    inference(superposition,[],[f44,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f53,f22])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ~r2_hidden(sK4,sK3) | sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.22/0.56    inference(subsumption_resolution,[],[f51,f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ~r1_tarski(sK4,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    r1_tarski(sK4,sK2) | ~r2_hidden(sK4,sK3) | sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.22/0.56    inference(superposition,[],[f44,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    sK2 = sK5(k2_tarski(sK1,sK2),sK4) | sK1 = sK5(k2_tarski(sK1,sK2),sK4)),
% 0.22/0.56    inference(resolution,[],[f48,f22])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    ( ! [X4] : (~r2_hidden(X4,sK3) | sK2 = sK5(k2_tarski(sK1,sK2),X4) | sK1 = sK5(k2_tarski(sK1,sK2),X4)) )),
% 0.22/0.56    inference(resolution,[],[f45,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK5(k2_tarski(sK1,sK2),X0),k2_tarski(sK1,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.56    inference(resolution,[],[f25,f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    r1_setfam_1(sK3,k2_tarski(sK1,sK2))),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK5(X1,X2),X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,sK5(X1,X2)) & r2_hidden(sK5(X1,X2),X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f7,f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X2,X1] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) => (r1_tarski(X2,sK5(X1,X2)) & r2_hidden(sK5(X1,X2),X1)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f7,plain,(
% 0.22/0.56    ! [X0,X1] : (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.56    inference(unused_predicate_definition_removal,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.22/0.56    inference(resolution,[],[f27,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 0.22/0.56    inference(equality_resolution,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.56    inference(nnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.56    inference(definition_folding,[],[f1,f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f17,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK6(X0,X1,X2) != X0 & sK6(X0,X1,X2) != X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (sK6(X0,X1,X2) = X0 | sK6(X0,X1,X2) = X1 | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.56    inference(rectify,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.56    inference(nnf_transformation,[],[f8])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(X0,sK5(k2_tarski(sK1,sK2),X0)) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.56    inference(resolution,[],[f26,f21])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,sK5(X1,X2))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (24779)------------------------------
% 0.22/0.56  % (24779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (24779)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (24779)Memory used [KB]: 6140
% 0.22/0.56  % (24779)Time elapsed: 0.133 s
% 0.22/0.56  % (24779)------------------------------
% 0.22/0.56  % (24779)------------------------------
% 0.22/0.56  % (24776)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.56  % (24775)Success in time 0.193 s
%------------------------------------------------------------------------------
