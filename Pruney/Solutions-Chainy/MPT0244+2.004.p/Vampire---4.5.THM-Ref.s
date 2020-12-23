%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 155 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 ( 615 expanded)
%              Number of equality atoms :   75 ( 294 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(subsumption_resolution,[],[f220,f166])).

fof(f166,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f165,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f165,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f164,f66])).

fof(f66,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(unit_resulting_resolution,[],[f58,f63])).

fof(f63,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f42])).

fof(f42,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | ~ r1_tarski(sK0,k1_tarski(sK1)) )
    & ( sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | r1_tarski(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ( k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | ~ r1_tarski(X0,k1_tarski(X1)) )
        & ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | r1_tarski(X0,k1_tarski(X1)) ) )
   => ( ( ( sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | ~ r1_tarski(sK0,k1_tarski(sK1)) )
      & ( sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | r1_tarski(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | ~ r1_tarski(X0,k1_tarski(X1)) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f18])).

% (22422)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f164,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f163,f67])).

fof(f67,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f43,f64])).

fof(f64,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK1)) ),
    inference(inner_rewriting,[],[f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f163,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_tarski(sK1),sK0)
    | sK0 = k1_tarski(sK1) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f40,plain,
    ( r1_tarski(sK0,k1_tarski(sK1))
    | k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f220,plain,(
    r2_hidden(sK1,sK0) ),
    inference(backward_demodulation,[],[f148,f213])).

fof(f213,plain,(
    sK1 = sK2(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f180,f62])).

fof(f62,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f180,plain,(
    r2_hidden(sK2(sK0,k1_xboole_0),k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f148,f161,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f161,plain,(
    r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f67,f66,f40])).

fof(f148,plain,(
    r2_hidden(sK2(sK0,k1_xboole_0),sK0) ),
    inference(unit_resulting_resolution,[],[f139,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f139,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f67,f43,f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:06:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (22426)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.21/0.48  % (22434)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.21/0.49  % (22450)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.21/0.50  % (22443)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.21/0.50  % (22446)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (22427)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.21/0.51  % (22437)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (22435)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 0.21/0.51  % (22427)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (22429)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.21/0.52  % (22447)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (22436)dis+1002_5_av=off:cond=on:gs=on:lma=on:nm=2:nwc=1:sd=3:ss=axioms:st=1.5:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f220,f166])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f165,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f164,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f58,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,sK0)),
% 0.21/0.52    inference(inner_rewriting,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1)))) => (((sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | ~r1_tarski(sK0,k1_tarski(sK1))) & (sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | r1_tarski(sK0,k1_tarski(sK1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0,X1] : (((k1_tarski(X1) != X0 & k1_xboole_0 != X0) | ~r1_tarski(X0,k1_tarski(X1))) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | r1_tarski(X0,k1_tarski(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  % (22422)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.21/0.52  fof(f18,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f17])).
% 0.21/0.52  fof(f17,conjecture,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    sK0 = k1_tarski(sK1) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    k1_xboole_0 != sK0),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f43,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k1_tarski(sK1))),
% 0.21/0.52    inference(inner_rewriting,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | ~r1_tarski(k1_tarski(sK1),sK0) | sK0 = k1_tarski(sK1)),
% 0.21/0.52    inference(resolution,[],[f40,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    r1_tarski(sK0,k1_tarski(sK1)) | k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    r2_hidden(sK1,sK0)),
% 0.21/0.52    inference(backward_demodulation,[],[f148,f213])).
% 0.21/0.52  fof(f213,plain,(
% 0.21/0.52    sK1 = sK2(sK0,k1_xboole_0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f180,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,k1_xboole_0),k1_tarski(sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f148,f161,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    r1_tarski(sK0,k1_tarski(sK1))),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f66,f40])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    r2_hidden(sK2(sK0,k1_xboole_0),sK0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f139,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ~r1_tarski(sK0,k1_xboole_0)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f67,f43,f49])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22427)------------------------------
% 0.21/0.52  % (22427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22427)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22427)Memory used [KB]: 1791
% 0.21/0.52  % (22427)Time elapsed: 0.099 s
% 0.21/0.52  % (22427)------------------------------
% 0.21/0.52  % (22427)------------------------------
% 0.21/0.52  % (22442)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 0.21/0.53  % (22425)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.21/0.53  % (22442)Refutation not found, incomplete strategy% (22442)------------------------------
% 0.21/0.53  % (22442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22442)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22442)Memory used [KB]: 1663
% 0.21/0.53  % (22442)Time elapsed: 0.111 s
% 0.21/0.53  % (22442)------------------------------
% 0.21/0.53  % (22442)------------------------------
% 0.21/0.53  % (22449)dis+11_2_add=large:afr=on:anc=none:gs=on:gsem=on:lwlo=on:nm=16:nwc=1:sd=1:ss=axioms:st=3.0:sos=on_4 on theBenchmark
% 0.21/0.53  % (22419)Success in time 0.165 s
%------------------------------------------------------------------------------
