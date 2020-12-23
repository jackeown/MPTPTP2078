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
% DateTime   : Thu Dec  3 12:37:46 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   46 (  96 expanded)
%              Number of leaves         :    9 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  187 ( 433 expanded)
%              Number of equality atoms :  129 ( 307 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f92,plain,(
    $false ),
    inference(subsumption_resolution,[],[f91,f62])).

fof(f62,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f61,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f60,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f60,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f40,f59])).

fof(f59,plain,(
    sK1 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,
    ( sK1 = sK3(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f52,f38])).

fof(f52,plain,
    ( v1_xboole_0(sK0)
    | sK1 = sK3(sK0) ),
    inference(resolution,[],[f29,f40])).

fof(f29,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f91,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK1 != sK1
    | sK0 != sK0 ),
    inference(superposition,[],[f54,f76])).

fof(f76,plain,(
    sK1 = sK2(sK1,sK1,sK1,sK0) ),
    inference(subsumption_resolution,[],[f75,f29])).

fof(f75,plain,
    ( sK1 = sK2(sK1,sK1,sK1,sK0)
    | r2_hidden(sK2(sK1,sK1,sK1,sK0),sK0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK1 = sK2(sK1,sK1,sK1,X0)
      | r2_hidden(sK2(sK1,sK1,sK1,X0),X0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( sK0 != X0
      | sK1 = sK2(sK1,sK1,sK1,X0)
      | sK1 = sK2(sK1,sK1,sK1,X0)
      | sK1 = sK2(sK1,sK1,sK1,X0)
      | r2_hidden(sK2(sK1,sK1,sK1,X0),X0) ) ),
    inference(superposition,[],[f43,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) = X2
      | sK2(X0,X1,X2,X3) = X1
      | sK2(X0,X1,X2,X3) = X0
      | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f23,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f43,plain,(
    sK0 != k1_enumset1(sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f42,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(sK1,sK1,sK1,X1),X1)
      | sK1 != sK2(sK1,sK1,sK1,X1)
      | sK0 != X1 ) ),
    inference(superposition,[],[f43,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK2(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (6232)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (6237)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (6237)Refutation not found, incomplete strategy% (6237)------------------------------
% 0.21/0.51  % (6237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6237)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6237)Memory used [KB]: 6268
% 0.21/0.51  % (6237)Time elapsed: 0.106 s
% 0.21/0.51  % (6237)------------------------------
% 0.21/0.51  % (6237)------------------------------
% 0.21/0.51  % (6226)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (6245)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.27/0.52  % (6236)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.52  % (6244)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.52  % (6224)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.52  % (6223)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (6228)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.53  % (6222)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.53  % (6222)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f92,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(subsumption_resolution,[],[f91,f62])).
% 1.27/0.53  fof(f62,plain,(
% 1.27/0.53    r2_hidden(sK1,sK0)),
% 1.27/0.53    inference(subsumption_resolution,[],[f61,f28])).
% 1.27/0.53  fof(f28,plain,(
% 1.27/0.53    k1_xboole_0 != sK0),
% 1.27/0.53    inference(cnf_transformation,[],[f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f18])).
% 1.27/0.53  fof(f18,plain,(
% 1.27/0.53    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f14,plain,(
% 1.27/0.53    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.27/0.53    inference(ennf_transformation,[],[f12])).
% 1.27/0.53  fof(f12,negated_conjecture,(
% 1.27/0.53    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.27/0.53    inference(negated_conjecture,[],[f11])).
% 1.27/0.53  fof(f11,conjecture,(
% 1.27/0.53    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.27/0.53  fof(f61,plain,(
% 1.27/0.53    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 1.27/0.53    inference(resolution,[],[f60,f38])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f16])).
% 1.27/0.53  fof(f16,plain,(
% 1.27/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.27/0.53    inference(ennf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.27/0.53  fof(f60,plain,(
% 1.27/0.53    v1_xboole_0(sK0) | r2_hidden(sK1,sK0)),
% 1.27/0.53    inference(superposition,[],[f40,f59])).
% 1.27/0.53  fof(f59,plain,(
% 1.27/0.53    sK1 = sK3(sK0)),
% 1.27/0.53    inference(subsumption_resolution,[],[f58,f28])).
% 1.27/0.53  fof(f58,plain,(
% 1.27/0.53    sK1 = sK3(sK0) | k1_xboole_0 = sK0),
% 1.27/0.53    inference(resolution,[],[f52,f38])).
% 1.27/0.53  fof(f52,plain,(
% 1.27/0.53    v1_xboole_0(sK0) | sK1 = sK3(sK0)),
% 1.27/0.53    inference(resolution,[],[f29,f40])).
% 1.27/0.53  fof(f29,plain,(
% 1.27/0.53    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 1.27/0.53    inference(cnf_transformation,[],[f19])).
% 1.27/0.53  fof(f40,plain,(
% 1.27/0.53    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f26])).
% 1.27/0.53  fof(f26,plain,(
% 1.27/0.53    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f25])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f17,plain,(
% 1.27/0.53    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 1.27/0.53    inference(ennf_transformation,[],[f13])).
% 1.27/0.53  fof(f13,plain,(
% 1.27/0.53    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 1.27/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 1.27/0.53  fof(f1,axiom,(
% 1.27/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.27/0.53  fof(f91,plain,(
% 1.27/0.53    ~r2_hidden(sK1,sK0)),
% 1.27/0.53    inference(trivial_inequality_removal,[],[f77])).
% 1.27/0.53  fof(f77,plain,(
% 1.27/0.53    ~r2_hidden(sK1,sK0) | sK1 != sK1 | sK0 != sK0),
% 1.27/0.53    inference(superposition,[],[f54,f76])).
% 1.27/0.53  fof(f76,plain,(
% 1.27/0.53    sK1 = sK2(sK1,sK1,sK1,sK0)),
% 1.27/0.53    inference(subsumption_resolution,[],[f75,f29])).
% 1.27/0.53  fof(f75,plain,(
% 1.27/0.53    sK1 = sK2(sK1,sK1,sK1,sK0) | r2_hidden(sK2(sK1,sK1,sK1,sK0),sK0)),
% 1.27/0.53    inference(equality_resolution,[],[f57])).
% 1.27/0.53  fof(f57,plain,(
% 1.27/0.53    ( ! [X0] : (sK0 != X0 | sK1 = sK2(sK1,sK1,sK1,X0) | r2_hidden(sK2(sK1,sK1,sK1,X0),X0)) )),
% 1.27/0.53    inference(duplicate_literal_removal,[],[f53])).
% 1.27/0.53  fof(f53,plain,(
% 1.27/0.53    ( ! [X0] : (sK0 != X0 | sK1 = sK2(sK1,sK1,sK1,X0) | sK1 = sK2(sK1,sK1,sK1,X0) | sK1 = sK2(sK1,sK1,sK1,X0) | r2_hidden(sK2(sK1,sK1,sK1,X0),X0)) )),
% 1.27/0.53    inference(superposition,[],[f43,f34])).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f24])).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 1.27/0.53  fof(f23,plain,(
% 1.27/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f22,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(rectify,[],[f21])).
% 1.27/0.53  fof(f21,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(flattening,[],[f20])).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.27/0.53    inference(nnf_transformation,[],[f15])).
% 1.27/0.53  fof(f15,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.27/0.53    inference(ennf_transformation,[],[f3])).
% 1.27/0.53  fof(f3,axiom,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    sK0 != k1_enumset1(sK1,sK1,sK1)),
% 1.27/0.53    inference(definition_unfolding,[],[f27,f42])).
% 1.27/0.53  fof(f42,plain,(
% 1.27/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.27/0.53    inference(definition_unfolding,[],[f39,f41])).
% 1.27/0.53  fof(f41,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f5])).
% 1.27/0.53  fof(f5,axiom,(
% 1.27/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.53  fof(f39,plain,(
% 1.27/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f4])).
% 1.27/0.53  fof(f4,axiom,(
% 1.27/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    sK0 != k1_tarski(sK1)),
% 1.27/0.53    inference(cnf_transformation,[],[f19])).
% 1.27/0.53  fof(f54,plain,(
% 1.27/0.53    ( ! [X1] : (~r2_hidden(sK2(sK1,sK1,sK1,X1),X1) | sK1 != sK2(sK1,sK1,sK1,X1) | sK0 != X1) )),
% 1.27/0.53    inference(superposition,[],[f43,f35])).
% 1.27/0.53  fof(f35,plain,(
% 1.27/0.53    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK2(X0,X1,X2,X3) != X0 | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f24])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (6222)------------------------------
% 1.27/0.53  % (6222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (6222)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (6222)Memory used [KB]: 1791
% 1.27/0.53  % (6222)Time elapsed: 0.124 s
% 1.27/0.53  % (6222)------------------------------
% 1.27/0.53  % (6222)------------------------------
% 1.27/0.53  % (6235)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.53  % (6221)Success in time 0.172 s
%------------------------------------------------------------------------------
