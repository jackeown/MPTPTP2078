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
% DateTime   : Thu Dec  3 12:37:47 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   38 (  79 expanded)
%              Number of leaves         :    7 (  22 expanded)
%              Depth                    :   16
%              Number of atoms          :  150 ( 358 expanded)
%              Number of equality atoms :  109 ( 259 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(subsumption_resolution,[],[f85,f23])).

fof(f23,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
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

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f85,plain,(
    sK0 = k1_tarski(sK1) ),
    inference(superposition,[],[f79,f33])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f79,plain,(
    sK0 = k2_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f78,f43])).

fof(f43,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f42,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,
    ( r2_hidden(sK1,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f32,f41])).

fof(f41,plain,(
    sK1 = sK3(sK0) ),
    inference(subsumption_resolution,[],[f40,f24])).

fof(f40,plain,
    ( sK1 = sK3(sK0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f25,f32])).

fof(f25,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f78,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,
    ( sK1 != sK1
    | sK0 = k2_tarski(sK1,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f30,f64])).

fof(f64,plain,(
    sK1 = sK2(sK1,sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f63])).

fof(f63,plain,
    ( sK0 != sK0
    | sK1 = sK2(sK1,sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,
    ( sK0 != sK0
    | sK1 = sK2(sK1,sK1,sK0)
    | sK1 = sK2(sK1,sK1,sK0) ),
    inference(superposition,[],[f23,f57])).

fof(f57,plain,(
    ! [X0] :
      ( k1_tarski(X0) = sK0
      | sK1 = sK2(X0,X0,sK0)
      | sK2(X0,X0,sK0) = X0 ) ),
    inference(duplicate_literal_removal,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_tarski(X0) = sK0
      | sK1 = sK2(X0,X0,sK0)
      | sK2(X0,X0,sK0) = X0
      | sK2(X0,X0,sK0) = X0 ) ),
    inference(superposition,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = sK0
      | sK1 = sK2(X0,X1,sK0)
      | sK2(X0,X1,sK0) = X1
      | sK2(X0,X1,sK0) = X0 ) ),
    inference(resolution,[],[f25,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) = X1
      | sK2(X0,X1,X2) = X0
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).

fof(f19,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK2(X0,X1,X2) != X0
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 18:40:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.24/0.53  % (32065)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.24/0.53  % (32038)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.24/0.53  % (32040)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.24/0.53  % (32036)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.24/0.53  % (32049)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.24/0.54  % (32049)Refutation found. Thanks to Tanya!
% 0.24/0.54  % SZS status Theorem for theBenchmark
% 0.24/0.54  % (32057)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.24/0.54  % SZS output start Proof for theBenchmark
% 0.24/0.54  fof(f99,plain,(
% 0.24/0.54    $false),
% 0.24/0.54    inference(subsumption_resolution,[],[f85,f23])).
% 0.24/0.54  fof(f23,plain,(
% 0.24/0.54    sK0 != k1_tarski(sK1)),
% 0.24/0.54    inference(cnf_transformation,[],[f15])).
% 0.24/0.54  fof(f15,plain,(
% 0.24/0.54    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 0.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 0.24/0.54  fof(f14,plain,(
% 0.24/0.54    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 0.24/0.54    introduced(choice_axiom,[])).
% 0.24/0.54  fof(f12,plain,(
% 0.24/0.54    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.24/0.54    inference(ennf_transformation,[],[f11])).
% 0.24/0.54  fof(f11,negated_conjecture,(
% 0.24/0.54    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.24/0.54    inference(negated_conjecture,[],[f10])).
% 0.24/0.54  fof(f10,conjecture,(
% 0.24/0.54    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.24/0.54  fof(f85,plain,(
% 0.24/0.54    sK0 = k1_tarski(sK1)),
% 0.24/0.54    inference(superposition,[],[f79,f33])).
% 0.24/0.54  fof(f33,plain,(
% 0.24/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f3])).
% 0.24/0.54  fof(f3,axiom,(
% 0.24/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.24/0.54  fof(f79,plain,(
% 0.24/0.54    sK0 = k2_tarski(sK1,sK1)),
% 0.24/0.54    inference(subsumption_resolution,[],[f78,f43])).
% 0.24/0.54  fof(f43,plain,(
% 0.24/0.54    r2_hidden(sK1,sK0)),
% 0.24/0.54    inference(subsumption_resolution,[],[f42,f24])).
% 0.24/0.54  fof(f24,plain,(
% 0.24/0.54    k1_xboole_0 != sK0),
% 0.24/0.54    inference(cnf_transformation,[],[f15])).
% 0.24/0.54  fof(f42,plain,(
% 0.24/0.54    r2_hidden(sK1,sK0) | k1_xboole_0 = sK0),
% 0.24/0.54    inference(superposition,[],[f32,f41])).
% 0.24/0.54  fof(f41,plain,(
% 0.24/0.54    sK1 = sK3(sK0)),
% 0.24/0.54    inference(subsumption_resolution,[],[f40,f24])).
% 0.24/0.54  fof(f40,plain,(
% 0.24/0.54    sK1 = sK3(sK0) | k1_xboole_0 = sK0),
% 0.24/0.54    inference(resolution,[],[f25,f32])).
% 0.24/0.54  fof(f25,plain,(
% 0.24/0.54    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.24/0.54    inference(cnf_transformation,[],[f15])).
% 0.24/0.54  fof(f32,plain,(
% 0.24/0.54    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.24/0.54    inference(cnf_transformation,[],[f22])).
% 0.24/0.54  fof(f22,plain,(
% 0.24/0.54    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f13,f21])).
% 0.24/0.54  fof(f21,plain,(
% 0.24/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.24/0.54    introduced(choice_axiom,[])).
% 0.24/0.54  fof(f13,plain,(
% 0.24/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.24/0.54    inference(ennf_transformation,[],[f1])).
% 0.24/0.54  fof(f1,axiom,(
% 0.24/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.24/0.54  fof(f78,plain,(
% 0.24/0.54    sK0 = k2_tarski(sK1,sK1) | ~r2_hidden(sK1,sK0)),
% 0.24/0.54    inference(trivial_inequality_removal,[],[f71])).
% 0.24/0.54  fof(f71,plain,(
% 0.24/0.54    sK1 != sK1 | sK0 = k2_tarski(sK1,sK1) | ~r2_hidden(sK1,sK0)),
% 0.24/0.54    inference(superposition,[],[f30,f64])).
% 0.24/0.54  fof(f64,plain,(
% 0.24/0.54    sK1 = sK2(sK1,sK1,sK0)),
% 0.24/0.54    inference(trivial_inequality_removal,[],[f63])).
% 0.24/0.54  fof(f63,plain,(
% 0.24/0.54    sK0 != sK0 | sK1 = sK2(sK1,sK1,sK0)),
% 0.24/0.54    inference(duplicate_literal_removal,[],[f62])).
% 0.24/0.54  fof(f62,plain,(
% 0.24/0.54    sK0 != sK0 | sK1 = sK2(sK1,sK1,sK0) | sK1 = sK2(sK1,sK1,sK0)),
% 0.24/0.54    inference(superposition,[],[f23,f57])).
% 0.24/0.54  fof(f57,plain,(
% 0.24/0.54    ( ! [X0] : (k1_tarski(X0) = sK0 | sK1 = sK2(X0,X0,sK0) | sK2(X0,X0,sK0) = X0) )),
% 0.24/0.54    inference(duplicate_literal_removal,[],[f45])).
% 0.24/0.54  fof(f45,plain,(
% 0.24/0.54    ( ! [X0] : (k1_tarski(X0) = sK0 | sK1 = sK2(X0,X0,sK0) | sK2(X0,X0,sK0) = X0 | sK2(X0,X0,sK0) = X0) )),
% 0.24/0.54    inference(superposition,[],[f39,f33])).
% 0.24/0.54  fof(f39,plain,(
% 0.24/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = sK0 | sK1 = sK2(X0,X1,sK0) | sK2(X0,X1,sK0) = X1 | sK2(X0,X1,sK0) = X0) )),
% 0.24/0.54    inference(resolution,[],[f25,f29])).
% 0.24/0.54  fof(f29,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f20])).
% 0.24/0.54  fof(f20,plain,(
% 0.24/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.24/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f19])).
% 0.24/0.54  fof(f19,plain,(
% 0.24/0.54    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.24/0.54    introduced(choice_axiom,[])).
% 0.24/0.54  fof(f18,plain,(
% 0.24/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.24/0.54    inference(rectify,[],[f17])).
% 0.24/0.54  fof(f17,plain,(
% 0.24/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.24/0.54    inference(flattening,[],[f16])).
% 0.24/0.54  fof(f16,plain,(
% 0.24/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.24/0.54    inference(nnf_transformation,[],[f2])).
% 0.24/0.54  fof(f2,axiom,(
% 0.24/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.24/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.24/0.54  fof(f30,plain,(
% 0.24/0.54    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK2(X0,X1,X2) != X0 | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.24/0.54    inference(cnf_transformation,[],[f20])).
% 0.24/0.54  % SZS output end Proof for theBenchmark
% 0.24/0.54  % (32049)------------------------------
% 0.24/0.54  % (32049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.54  % (32049)Termination reason: Refutation
% 0.24/0.54  
% 0.24/0.54  % (32049)Memory used [KB]: 10746
% 0.24/0.54  % (32049)Time elapsed: 0.103 s
% 0.24/0.54  % (32049)------------------------------
% 0.24/0.54  % (32049)------------------------------
% 1.34/0.55  % (32030)Success in time 0.167 s
%------------------------------------------------------------------------------
