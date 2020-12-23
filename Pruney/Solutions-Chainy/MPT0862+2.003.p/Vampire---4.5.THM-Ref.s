%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 114 expanded)
%              Number of leaves         :   12 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  195 ( 439 expanded)
%              Number of equality atoms :  118 ( 290 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f116,f120])).

fof(f120,plain,
    ( spl6_3
    | spl6_2 ),
    inference(avatar_split_clause,[],[f119,f86,f91])).

fof(f91,plain,
    ( spl6_3
  <=> sQ5_eqProxy(sK2,k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f86,plain,
    ( spl6_2
  <=> sQ5_eqProxy(sK3,k2_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f119,plain,
    ( sQ5_eqProxy(sK3,k2_mcart_1(sK0))
    | sQ5_eqProxy(sK2,k2_mcart_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( sQ5_eqProxy(sK3,k2_mcart_1(sK0))
    | sQ5_eqProxy(sK2,k2_mcart_1(sK0))
    | sQ5_eqProxy(sK2,k2_mcart_1(sK0)) ),
    inference(resolution,[],[f111,f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X1] :
      ( sQ5_eqProxy(X2,X5)
      | sQ5_eqProxy(X1,X5)
      | sQ5_eqProxy(X0,X5)
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_proxy_replacement,[],[f68,f69,f69,f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f68,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK4(X0,X1,X2,X3) != X2
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X2
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X0
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK4(X0,X1,X2,X3) != X2
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X2
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X0
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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

fof(f111,plain,(
    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(resolution,[],[f46,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f46,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f23,f45,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f26,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( sK3 != k2_mcart_1(sK0)
        & sK2 != k2_mcart_1(sK0) )
      | sK1 != k1_mcart_1(sK0) )
    & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ( k2_mcart_1(X0) != X3
            & k2_mcart_1(X0) != X2 )
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) )
   => ( ( ( sK3 != k2_mcart_1(sK0)
          & sK2 != k2_mcart_1(sK0) )
        | sK1 != k1_mcart_1(sK0) )
      & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

fof(f116,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f115,f82])).

fof(f82,plain,
    ( spl6_1
  <=> sQ5_eqProxy(sK1,k1_mcart_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f115,plain,(
    sQ5_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( sQ5_eqProxy(sK1,k1_mcart_1(sK0))
    | sQ5_eqProxy(sK1,k1_mcart_1(sK0))
    | sQ5_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(resolution,[],[f110,f79])).

fof(f110,plain,(
    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(resolution,[],[f46,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f71,f91,f82])).

fof(f71,plain,
    ( ~ sQ5_eqProxy(sK2,k2_mcart_1(sK0))
    | ~ sQ5_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f24,f69,f69])).

fof(f24,plain,
    ( sK2 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f70,f86,f82])).

fof(f70,plain,
    ( ~ sQ5_eqProxy(sK3,k2_mcart_1(sK0))
    | ~ sQ5_eqProxy(sK1,k1_mcart_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f25,f69,f69])).

fof(f25,plain,
    ( sK3 != k2_mcart_1(sK0)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:16:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.55  % (15977)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (15969)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (15959)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (15969)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f89,f94,f116,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    spl6_3 | spl6_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f119,f86,f91])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl6_3 <=> sQ5_eqProxy(sK2,k2_mcart_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl6_2 <=> sQ5_eqProxy(sK3,k2_mcart_1(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    sQ5_eqProxy(sK3,k2_mcart_1(sK0)) | sQ5_eqProxy(sK2,k2_mcart_1(sK0))),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f117])).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    sQ5_eqProxy(sK3,k2_mcart_1(sK0)) | sQ5_eqProxy(sK2,k2_mcart_1(sK0)) | sQ5_eqProxy(sK2,k2_mcart_1(sK0))),
% 0.21/0.55    inference(resolution,[],[f111,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X2,X0,X5,X1] : (sQ5_eqProxy(X2,X5) | sQ5_eqProxy(X1,X5) | sQ5_eqProxy(X0,X5) | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 0.21/0.55    inference(equality_proxy_replacement,[],[f68,f69,f69,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.55    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 0.21/0.55    inference(equality_resolution,[],[f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 0.21/0.55    inference(definition_unfolding,[],[f36,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X2 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X2 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X0 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.56    inference(rectify,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.21/0.56    inference(nnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    r2_hidden(k2_mcart_1(sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.21/0.56    inference(resolution,[],[f46,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    r2_hidden(sK0,k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK2,sK2,sK2,sK3)))),
% 0.21/0.56    inference(definition_unfolding,[],[f23,f45,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f27,f30])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f26,f44])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3)))) => (((sK3 != k2_mcart_1(sK0) & sK2 != k2_mcart_1(sK0)) | sK1 != k1_mcart_1(sK0)) & r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),k2_tarski(sK2,sK3))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.56    inference(negated_conjecture,[],[f8])).
% 0.21/0.56  fof(f8,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    spl6_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f115,f82])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    spl6_1 <=> sQ5_eqProxy(sK1,k1_mcart_1(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    sQ5_eqProxy(sK1,k1_mcart_1(sK0))),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    sQ5_eqProxy(sK1,k1_mcart_1(sK0)) | sQ5_eqProxy(sK1,k1_mcart_1(sK0)) | sQ5_eqProxy(sK1,k1_mcart_1(sK0))),
% 0.21/0.56    inference(resolution,[],[f110,f79])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    r2_hidden(k1_mcart_1(sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.21/0.56    inference(resolution,[],[f46,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ~spl6_1 | ~spl6_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f71,f91,f82])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ~sQ5_eqProxy(sK2,k2_mcart_1(sK0)) | ~sQ5_eqProxy(sK1,k1_mcart_1(sK0))),
% 0.21/0.56    inference(equality_proxy_replacement,[],[f24,f69,f69])).
% 1.31/0.56  fof(f24,plain,(
% 1.31/0.56    sK2 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  fof(f89,plain,(
% 1.31/0.56    ~spl6_1 | ~spl6_2),
% 1.31/0.56    inference(avatar_split_clause,[],[f70,f86,f82])).
% 1.31/0.56  fof(f70,plain,(
% 1.31/0.56    ~sQ5_eqProxy(sK3,k2_mcart_1(sK0)) | ~sQ5_eqProxy(sK1,k1_mcart_1(sK0))),
% 1.31/0.56    inference(equality_proxy_replacement,[],[f25,f69,f69])).
% 1.31/0.56  fof(f25,plain,(
% 1.31/0.56    sK3 != k2_mcart_1(sK0) | sK1 != k1_mcart_1(sK0)),
% 1.31/0.56    inference(cnf_transformation,[],[f14])).
% 1.31/0.56  % SZS output end Proof for theBenchmark
% 1.31/0.56  % (15969)------------------------------
% 1.31/0.56  % (15969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.56  % (15969)Termination reason: Refutation
% 1.31/0.56  
% 1.31/0.56  % (15969)Memory used [KB]: 6268
% 1.31/0.56  % (15969)Time elapsed: 0.067 s
% 1.31/0.56  % (15969)------------------------------
% 1.31/0.56  % (15969)------------------------------
% 1.31/0.56  % (15961)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.56  % (15953)Success in time 0.193 s
%------------------------------------------------------------------------------
