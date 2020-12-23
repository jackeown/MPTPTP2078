%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:14 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 192 expanded)
%              Number of equality atoms :   69 (  90 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f54,f60])).

fof(f60,plain,(
    sK2 = k1_mcart_1(sK1) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,
    ( sK2 = k1_mcart_1(sK1)
    | sK2 = k1_mcart_1(sK1) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
    r2_hidden(k1_mcart_1(sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[],[f23,f34])).

fof(f34,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f19,f33])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
      | sK2 != k1_mcart_1(sK1) )
    & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | k1_mcart_1(X0) != X1 )
        & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
        | sK2 != k1_mcart_1(sK1) )
      & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_enumset1(X0,X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f25,f39])).

fof(f39,plain,(
    ! [X0,X1] : sP0(X1,X0,k1_enumset1(X0,X0,X1)) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(definition_folding,[],[f1,f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK4(X0,X1,X2) != X0
              & sK4(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X0
            | sK4(X0,X1,X2) = X1
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X0
            & sK4(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X0
          | sK4(X0,X1,X2) = X1
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    r2_hidden(k2_mcart_1(sK1),sK3) ),
    inference(resolution,[],[f24,f34])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,
    ( ~ r2_hidden(k2_mcart_1(sK1),sK3)
    | sK2 != k1_mcart_1(sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % WCLimit    : 600
% 0.15/0.36  % DateTime   : Tue Dec  1 11:56:00 EST 2020
% 0.15/0.36  % CPUTime    : 
% 1.38/0.59  % (16420)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.59  % (16436)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.38/0.60  % (16421)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.60  % (16428)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.60  % (16420)Refutation found. Thanks to Tanya!
% 1.38/0.60  % SZS status Theorem for theBenchmark
% 1.38/0.60  % SZS output start Proof for theBenchmark
% 1.38/0.60  fof(f63,plain,(
% 1.38/0.60    $false),
% 1.38/0.60    inference(global_subsumption,[],[f20,f54,f60])).
% 1.38/0.60  fof(f60,plain,(
% 1.38/0.60    sK2 = k1_mcart_1(sK1)),
% 1.38/0.60    inference(duplicate_literal_removal,[],[f59])).
% 1.38/0.60  fof(f59,plain,(
% 1.38/0.60    sK2 = k1_mcart_1(sK1) | sK2 = k1_mcart_1(sK1)),
% 1.38/0.60    inference(resolution,[],[f56,f53])).
% 1.38/0.60  fof(f53,plain,(
% 1.38/0.60    r2_hidden(k1_mcart_1(sK1),k1_enumset1(sK2,sK2,sK2))),
% 1.38/0.60    inference(resolution,[],[f23,f34])).
% 1.38/0.60  fof(f34,plain,(
% 1.38/0.60    r2_hidden(sK1,k2_zfmisc_1(k1_enumset1(sK2,sK2,sK2),sK3))),
% 1.38/0.60    inference(definition_unfolding,[],[f19,f33])).
% 1.38/0.60  fof(f33,plain,(
% 1.38/0.60    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.38/0.60    inference(definition_unfolding,[],[f21,f22])).
% 1.38/0.60  fof(f22,plain,(
% 1.38/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f3])).
% 1.38/0.60  fof(f3,axiom,(
% 1.38/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.60  fof(f21,plain,(
% 1.38/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f2])).
% 1.38/0.60  fof(f2,axiom,(
% 1.38/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.60  fof(f19,plain,(
% 1.38/0.60    r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.38/0.60    inference(cnf_transformation,[],[f12])).
% 1.38/0.60  fof(f12,plain,(
% 1.38/0.60    (~r2_hidden(k2_mcart_1(sK1),sK3) | sK2 != k1_mcart_1(sK1)) & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3))),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f7,f11])).
% 1.38/0.60  fof(f11,plain,(
% 1.38/0.60    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))) => ((~r2_hidden(k2_mcart_1(sK1),sK3) | sK2 != k1_mcart_1(sK1)) & r2_hidden(sK1,k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f7,plain,(
% 1.38/0.60    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 1.38/0.60    inference(ennf_transformation,[],[f6])).
% 1.38/0.60  fof(f6,negated_conjecture,(
% 1.38/0.60    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.38/0.60    inference(negated_conjecture,[],[f5])).
% 1.38/0.60  fof(f5,conjecture,(
% 1.38/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).
% 1.38/0.60  fof(f23,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f8])).
% 1.38/0.60  fof(f8,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.38/0.60    inference(ennf_transformation,[],[f4])).
% 1.38/0.60  fof(f4,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.38/0.60  fof(f56,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_enumset1(X0,X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.38/0.60    inference(resolution,[],[f25,f39])).
% 1.38/0.60  fof(f39,plain,(
% 1.38/0.60    ( ! [X0,X1] : (sP0(X1,X0,k1_enumset1(X0,X0,X1))) )),
% 1.38/0.60    inference(equality_resolution,[],[f36])).
% 1.38/0.60  fof(f36,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.38/0.60    inference(definition_unfolding,[],[f31,f22])).
% 1.38/0.60  fof(f31,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.38/0.60    inference(cnf_transformation,[],[f18])).
% 1.38/0.60  fof(f18,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.38/0.60    inference(nnf_transformation,[],[f10])).
% 1.38/0.60  fof(f10,plain,(
% 1.38/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.38/0.60    inference(definition_folding,[],[f1,f9])).
% 1.38/0.60  fof(f9,plain,(
% 1.38/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.38/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.60  fof(f1,axiom,(
% 1.38/0.60    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.38/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.38/0.60  fof(f25,plain,(
% 1.38/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.38/0.60    inference(cnf_transformation,[],[f17])).
% 1.38/0.60  fof(f17,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.38/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f15,f16])).
% 1.38/0.60  fof(f16,plain,(
% 1.38/0.60    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.38/0.60    introduced(choice_axiom,[])).
% 1.38/0.60  fof(f15,plain,(
% 1.38/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.38/0.60    inference(rectify,[],[f14])).
% 1.38/0.60  fof(f14,plain,(
% 1.38/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.38/0.60    inference(flattening,[],[f13])).
% 1.38/0.60  fof(f13,plain,(
% 1.38/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.38/0.60    inference(nnf_transformation,[],[f9])).
% 1.38/0.60  fof(f54,plain,(
% 1.38/0.60    r2_hidden(k2_mcart_1(sK1),sK3)),
% 1.38/0.60    inference(resolution,[],[f24,f34])).
% 1.38/0.60  fof(f24,plain,(
% 1.38/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.38/0.60    inference(cnf_transformation,[],[f8])).
% 1.38/0.60  fof(f20,plain,(
% 1.38/0.60    ~r2_hidden(k2_mcart_1(sK1),sK3) | sK2 != k1_mcart_1(sK1)),
% 1.38/0.60    inference(cnf_transformation,[],[f12])).
% 1.38/0.60  % SZS output end Proof for theBenchmark
% 1.38/0.60  % (16420)------------------------------
% 1.38/0.60  % (16420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.60  % (16420)Termination reason: Refutation
% 1.38/0.60  
% 1.38/0.60  % (16420)Memory used [KB]: 10746
% 1.38/0.60  % (16420)Time elapsed: 0.127 s
% 1.38/0.60  % (16420)------------------------------
% 1.38/0.60  % (16420)------------------------------
% 1.38/0.60  % (16437)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.60  % (16413)Success in time 0.227 s
%------------------------------------------------------------------------------
