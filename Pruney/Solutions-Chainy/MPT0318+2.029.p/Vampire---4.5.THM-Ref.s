%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  80 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 246 expanded)
%              Number of equality atoms :  131 ( 205 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f77,plain,(
    $false ),
    inference(subsumption_resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f57,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f38,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

fof(f57,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f36,f38])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f72,plain,(
    r2_hidden(sK1,k1_xboole_0) ),
    inference(superposition,[],[f55,f67])).

fof(f67,plain,(
    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f66,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f66,plain,
    ( k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f65])).

fof(f65,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f64])).

% (24952)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f64,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(superposition,[],[f26,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) ),
    inference(subsumption_resolution,[],[f61,f21])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(superposition,[],[f26,f39])).

fof(f39,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f22,f38,f38])).

fof(f22,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

% (24949)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f55,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f45])).

% (24950)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f25])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

% (24949)Refutation not found, incomplete strategy% (24949)------------------------------
% (24949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24949)Termination reason: Refutation not found, incomplete strategy

% (24949)Memory used [KB]: 1663
% (24949)Time elapsed: 0.098 s
% (24949)------------------------------
% (24949)------------------------------
fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24970)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (24951)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (24962)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (24970)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (24954)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f72,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f57,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f24,f38,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f23,f25])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.51    inference(equality_resolution,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f36,f38])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 0.21/0.51    inference(nnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    r2_hidden(sK1,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f55,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f66,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.51  % (24952)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.51    inference(superposition,[],[f26,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0) | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f61,f21])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_enumset1(sK1,sK1,sK1) | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.21/0.51    inference(superposition,[],[f26,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k1_enumset1(sK1,sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK0)),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f38,f38])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  % (24949)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.51    inference(nnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 0.21/0.51    inference(equality_resolution,[],[f45])).
% 0.21/0.51  % (24950)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.51    inference(definition_unfolding,[],[f30,f25])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  % (24949)Refutation not found, incomplete strategy% (24949)------------------------------
% 0.21/0.51  % (24949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24949)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24949)Memory used [KB]: 1663
% 0.21/0.51  % (24949)Time elapsed: 0.098 s
% 0.21/0.51  % (24949)------------------------------
% 0.21/0.51  % (24949)------------------------------
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.51    inference(rectify,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (24970)------------------------------
% 0.21/0.51  % (24970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24970)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (24970)Memory used [KB]: 6268
% 0.21/0.51  % (24970)Time elapsed: 0.061 s
% 0.21/0.51  % (24970)------------------------------
% 0.21/0.51  % (24970)------------------------------
% 0.21/0.52  % (24945)Success in time 0.153 s
%------------------------------------------------------------------------------
