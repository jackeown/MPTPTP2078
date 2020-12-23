%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:52 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   53 (  85 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 331 expanded)
%              Number of equality atoms :   88 ( 174 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f81,f91])).

fof(f91,plain,(
    ~ spl6_1 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl6_1 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( sK1 != sK1
    | ~ spl6_1 ),
    inference(superposition,[],[f25,f66])).

fof(f66,plain,
    ( sK1 = sK3
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_1
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f25,plain,(
    sK1 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK1 != sK3
    & sK1 != sK2
    & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK1 != sK3
      & sK1 != sK2
      & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f81,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f80])).

fof(f80,plain,
    ( $false
    | ~ spl6_2 ),
    inference(trivial_inequality_removal,[],[f79])).

fof(f79,plain,
    ( sK1 != sK1
    | ~ spl6_2 ),
    inference(superposition,[],[f24,f70])).

fof(f70,plain,
    ( sK1 = sK2
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl6_2
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f71,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f62,f68,f64])).

fof(f62,plain,
    ( sK1 = sK2
    | sK1 = sK3 ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f9])).

fof(f9,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f58,plain,(
    ! [X2,X3] :
      ( ~ sP0(X3,X2,k2_enumset1(sK1,sK1,sK1,sK1))
      | sK2 = X2
      | sK3 = X2 ) ),
    inference(resolution,[],[f54,f44])).

fof(f44,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | ~ sP0(X0,X4,X2) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).

fof(f20,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
      | sK3 = X0
      | sK2 = X0 ) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f23,f39,f27])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X3,k2_enumset1(X0,X0,X0,X2))
      | X1 = X2
      | ~ r2_hidden(X1,X3)
      | X0 = X1 ) ),
    inference(resolution,[],[f47,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_enumset1(X0,X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f31,f45])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:36:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (6836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (6827)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (6813)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (6825)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  % (6825)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.56/0.56  % SZS output start Proof for theBenchmark
% 1.56/0.56  fof(f92,plain,(
% 1.56/0.56    $false),
% 1.56/0.56    inference(avatar_sat_refutation,[],[f71,f81,f91])).
% 1.56/0.56  fof(f91,plain,(
% 1.56/0.56    ~spl6_1),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f90])).
% 1.56/0.56  fof(f90,plain,(
% 1.56/0.56    $false | ~spl6_1),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f89])).
% 1.56/0.56  fof(f89,plain,(
% 1.56/0.56    sK1 != sK1 | ~spl6_1),
% 1.56/0.56    inference(superposition,[],[f25,f66])).
% 1.56/0.56  fof(f66,plain,(
% 1.56/0.56    sK1 = sK3 | ~spl6_1),
% 1.56/0.56    inference(avatar_component_clause,[],[f64])).
% 1.56/0.56  fof(f64,plain,(
% 1.56/0.56    spl6_1 <=> sK1 = sK3),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.56/0.56  fof(f25,plain,(
% 1.56/0.56    sK1 != sK3),
% 1.56/0.56    inference(cnf_transformation,[],[f12])).
% 1.56/0.56  fof(f12,plain,(
% 1.56/0.56    sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f7,f11])).
% 1.56/0.56  fof(f11,plain,(
% 1.56/0.56    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK1 != sK3 & sK1 != sK2 & r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f7,plain,(
% 1.56/0.56    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.56/0.56    inference(ennf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.56/0.56    inference(negated_conjecture,[],[f5])).
% 1.56/0.56  fof(f5,conjecture,(
% 1.56/0.56    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.56/0.56  fof(f81,plain,(
% 1.56/0.56    ~spl6_2),
% 1.56/0.56    inference(avatar_contradiction_clause,[],[f80])).
% 1.56/0.56  fof(f80,plain,(
% 1.56/0.56    $false | ~spl6_2),
% 1.56/0.56    inference(trivial_inequality_removal,[],[f79])).
% 1.56/0.56  fof(f79,plain,(
% 1.56/0.56    sK1 != sK1 | ~spl6_2),
% 1.56/0.56    inference(superposition,[],[f24,f70])).
% 1.56/0.56  fof(f70,plain,(
% 1.56/0.56    sK1 = sK2 | ~spl6_2),
% 1.56/0.56    inference(avatar_component_clause,[],[f68])).
% 1.56/0.56  fof(f68,plain,(
% 1.56/0.56    spl6_2 <=> sK1 = sK2),
% 1.56/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.56/0.56  fof(f24,plain,(
% 1.56/0.56    sK1 != sK2),
% 1.56/0.56    inference(cnf_transformation,[],[f12])).
% 1.56/0.56  fof(f71,plain,(
% 1.56/0.56    spl6_1 | spl6_2),
% 1.56/0.56    inference(avatar_split_clause,[],[f62,f68,f64])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    sK1 = sK2 | sK1 = sK3),
% 1.56/0.56    inference(resolution,[],[f58,f45])).
% 1.56/0.56  fof(f45,plain,(
% 1.56/0.56    ( ! [X0,X1] : (sP0(X1,X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.56/0.56    inference(equality_resolution,[],[f42])).
% 1.56/0.56  fof(f42,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.56/0.56    inference(definition_unfolding,[],[f37,f27])).
% 1.56/0.56  fof(f27,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f4])).
% 1.56/0.56  fof(f4,axiom,(
% 1.56/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 1.56/0.56  fof(f37,plain,(
% 1.56/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.56/0.56    inference(cnf_transformation,[],[f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.56/0.56    inference(nnf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,plain,(
% 1.56/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.56/0.56    inference(definition_folding,[],[f2,f9])).
% 1.56/0.56  fof(f9,plain,(
% 1.56/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.56/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.56/0.56  fof(f2,axiom,(
% 1.56/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.56/0.56  fof(f58,plain,(
% 1.56/0.56    ( ! [X2,X3] : (~sP0(X3,X2,k2_enumset1(sK1,sK1,sK1,sK1)) | sK2 = X2 | sK3 = X2) )),
% 1.56/0.56    inference(resolution,[],[f54,f44])).
% 1.56/0.56  fof(f44,plain,(
% 1.56/0.56    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | ~sP0(X0,X4,X2)) )),
% 1.56/0.56    inference(equality_resolution,[],[f32])).
% 1.56/0.56  fof(f32,plain,(
% 1.56/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.56/0.56    inference(cnf_transformation,[],[f21])).
% 1.56/0.56  fof(f21,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f19,f20])).
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X0 & sK5(X0,X1,X2) != X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X0 | sK5(X0,X1,X2) = X1 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  fof(f19,plain,(
% 1.56/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.56/0.56    inference(rectify,[],[f18])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.56/0.57    inference(flattening,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.56/0.57    inference(nnf_transformation,[],[f9])).
% 1.56/0.57  fof(f54,plain,(
% 1.56/0.57    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) | sK3 = X0 | sK2 = X0) )),
% 1.56/0.57    inference(resolution,[],[f48,f40])).
% 1.56/0.57  fof(f40,plain,(
% 1.56/0.57    r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.56/0.57    inference(definition_unfolding,[],[f23,f39,f27])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.56/0.57    inference(definition_unfolding,[],[f26,f27])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    r1_tarski(k1_tarski(sK1),k2_tarski(sK2,sK3))),
% 1.56/0.57    inference(cnf_transformation,[],[f12])).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(X3,k2_enumset1(X0,X0,X0,X2)) | X1 = X2 | ~r2_hidden(X1,X3) | X0 = X1) )),
% 1.56/0.57    inference(resolution,[],[f47,f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f16])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(rectify,[],[f13])).
% 1.56/0.57  fof(f13,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,plain,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.57    inference(ennf_transformation,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.57  fof(f47,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_enumset1(X0,X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.56/0.57    inference(resolution,[],[f31,f45])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.56/0.57    inference(cnf_transformation,[],[f21])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (6825)------------------------------
% 1.56/0.57  % (6825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (6825)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (6825)Memory used [KB]: 6268
% 1.56/0.57  % (6825)Time elapsed: 0.122 s
% 1.56/0.57  % (6825)------------------------------
% 1.56/0.57  % (6825)------------------------------
% 1.56/0.57  % (6804)Success in time 0.206 s
%------------------------------------------------------------------------------
