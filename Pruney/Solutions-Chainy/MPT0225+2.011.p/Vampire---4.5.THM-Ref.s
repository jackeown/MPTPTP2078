%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 123 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   13
%              Number of atoms          :  197 ( 424 expanded)
%              Number of equality atoms :  108 ( 292 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f820,plain,(
    $false ),
    inference(subsumption_resolution,[],[f819,f714])).

fof(f714,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f713,f195])).

fof(f195,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | sK0 != sK1 ),
    inference(subsumption_resolution,[],[f193,f80])).

fof(f80,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f193,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | sK0 != sK1
    | k1_xboole_0 != k1_tarski(sK0) ),
    inference(resolution,[],[f122,f133])).

fof(f133,plain,
    ( r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | sK0 != sK1
    | k1_xboole_0 != k1_tarski(sK0) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | sK0 != sK1
    | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0))
    | sK0 != sK1 ),
    inference(resolution,[],[f101,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tarski(sK1))
      | r1_xboole_0(X0,k1_tarski(sK0))
      | sK0 != sK1 ) ),
    inference(superposition,[],[f76,f48])).

fof(f48,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( sK0 = sK1
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
    & ( sK0 != sK1
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
        & ( X0 != X1
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) )
   => ( ( sK0 = sK1
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) )
      & ( sK0 != sK1
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
      & ( X0 != X1
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f101,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 != k1_tarski(sK0)
    | sK0 != sK1 ),
    inference(superposition,[],[f72,f48])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,k1_tarski(X1))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f63,f80])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f713,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | sK0 = sK1 ),
    inference(duplicate_literal_removal,[],[f705])).

fof(f705,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | sK0 = sK1
    | sK0 = sK1 ),
    inference(superposition,[],[f49,f701])).

fof(f701,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f692])).

fof(f692,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | sK0 = sK1
    | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f49,f142])).

fof(f142,plain,(
    ! [X2,X1] :
      ( k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f49,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f819,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f720,f82])).

fof(f82,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f720,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f109,f717])).

fof(f717,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f712,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f712,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f710])).

fof(f710,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f72,f701])).

fof(f109,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f104,f64])).

fof(f104,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 != sK1 ),
    inference(superposition,[],[f73,f48])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (25243)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (25241)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (25237)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (25252)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (25242)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (25267)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (25264)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (25264)Refutation not found, incomplete strategy% (25264)------------------------------
% 0.20/0.51  % (25264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25264)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25264)Memory used [KB]: 6268
% 0.20/0.51  % (25264)Time elapsed: 0.103 s
% 0.20/0.51  % (25264)------------------------------
% 0.20/0.51  % (25264)------------------------------
% 0.20/0.51  % (25246)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (25258)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (25252)Refutation not found, incomplete strategy% (25252)------------------------------
% 0.20/0.51  % (25252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25252)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (25252)Memory used [KB]: 1663
% 0.20/0.51  % (25252)Time elapsed: 0.099 s
% 0.20/0.51  % (25252)------------------------------
% 0.20/0.51  % (25252)------------------------------
% 0.20/0.52  % (25256)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (25256)Refutation not found, incomplete strategy% (25256)------------------------------
% 0.20/0.52  % (25256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25256)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25256)Memory used [KB]: 1663
% 0.20/0.52  % (25256)Time elapsed: 0.114 s
% 0.20/0.52  % (25256)------------------------------
% 0.20/0.52  % (25256)------------------------------
% 0.20/0.52  % (25245)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (25267)Refutation not found, incomplete strategy% (25267)------------------------------
% 0.20/0.52  % (25267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25267)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25267)Memory used [KB]: 1663
% 0.20/0.52  % (25267)Time elapsed: 0.003 s
% 0.20/0.52  % (25267)------------------------------
% 0.20/0.52  % (25267)------------------------------
% 0.20/0.52  % (25239)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (25261)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (25257)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (25249)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (25238)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (25250)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (25238)Refutation not found, incomplete strategy% (25238)------------------------------
% 0.20/0.53  % (25238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (25238)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (25238)Memory used [KB]: 1663
% 0.20/0.53  % (25238)Time elapsed: 0.115 s
% 0.20/0.53  % (25238)------------------------------
% 0.20/0.53  % (25238)------------------------------
% 0.20/0.53  % (25253)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (25240)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (25244)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (25262)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (25254)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (25259)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (25260)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (25247)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.54  % (25265)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (25266)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (25265)Refutation not found, incomplete strategy% (25265)------------------------------
% 0.20/0.54  % (25265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25265)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (25265)Memory used [KB]: 6140
% 0.20/0.54  % (25265)Time elapsed: 0.129 s
% 0.20/0.54  % (25265)------------------------------
% 0.20/0.54  % (25265)------------------------------
% 0.20/0.54  % (25262)Refutation not found, incomplete strategy% (25262)------------------------------
% 0.20/0.54  % (25262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (25263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (25255)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (25248)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.55  % (25255)Refutation not found, incomplete strategy% (25255)------------------------------
% 0.20/0.55  % (25255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25248)Refutation not found, incomplete strategy% (25248)------------------------------
% 0.20/0.55  % (25248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25255)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25255)Memory used [KB]: 1663
% 0.20/0.55  % (25255)Time elapsed: 0.140 s
% 0.20/0.55  % (25255)------------------------------
% 0.20/0.55  % (25255)------------------------------
% 0.20/0.55  % (25248)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25248)Memory used [KB]: 6140
% 0.20/0.55  % (25248)Time elapsed: 0.141 s
% 0.20/0.55  % (25248)------------------------------
% 0.20/0.55  % (25248)------------------------------
% 0.20/0.55  % (25254)Refutation not found, incomplete strategy% (25254)------------------------------
% 0.20/0.55  % (25254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25254)Memory used [KB]: 10618
% 0.20/0.55  % (25254)Time elapsed: 0.130 s
% 0.20/0.55  % (25254)------------------------------
% 0.20/0.55  % (25254)------------------------------
% 0.20/0.55  % (25262)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25262)Memory used [KB]: 10618
% 0.20/0.55  % (25262)Time elapsed: 0.128 s
% 0.20/0.55  % (25262)------------------------------
% 0.20/0.55  % (25262)------------------------------
% 0.20/0.55  % (25246)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f820,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f819,f714])).
% 0.20/0.57  fof(f714,plain,(
% 0.20/0.57    k1_xboole_0 != k1_tarski(sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f713,f195])).
% 0.20/0.57  fof(f195,plain,(
% 0.20/0.57    k1_xboole_0 != k1_tarski(sK0) | sK0 != sK1),
% 0.20/0.57    inference(subsumption_resolution,[],[f193,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.57    inference(equality_resolution,[],[f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.57    inference(equality_resolution,[],[f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f42,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(rectify,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.57  fof(f193,plain,(
% 0.20/0.57    ~r2_hidden(sK0,k1_tarski(sK0)) | sK0 != sK1 | k1_xboole_0 != k1_tarski(sK0)),
% 0.20/0.57    inference(resolution,[],[f122,f133])).
% 0.20/0.57  fof(f133,plain,(
% 0.20/0.57    r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | sK0 != sK1 | k1_xboole_0 != k1_tarski(sK0)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f132])).
% 0.20/0.57  fof(f132,plain,(
% 0.20/0.57    k1_xboole_0 != k1_tarski(sK0) | sK0 != sK1 | r1_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) | sK0 != sK1),
% 0.20/0.57    inference(resolution,[],[f101,f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,k1_tarski(sK1)) | r1_xboole_0(X0,k1_tarski(sK0)) | sK0 != sK1) )),
% 0.20/0.57    inference(superposition,[],[f76,f48])).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    (sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))) => ((sK0 = sK1 | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) & (sK0 != sK1 | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ? [X0,X1] : ((X0 = X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) & (X0 != X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <~> X0 != X1)),
% 0.20/0.57    inference(ennf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.57    inference(negated_conjecture,[],[f21])).
% 0.20/0.57  fof(f21,conjecture,(
% 0.20/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.57  fof(f101,plain,(
% 0.20/0.57    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 != k1_tarski(sK0) | sK0 != sK1),
% 0.20/0.57    inference(superposition,[],[f72,f48])).
% 0.20/0.57  fof(f72,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.57  fof(f122,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,k1_tarski(X1)) | ~r2_hidden(X1,X0)) )),
% 0.20/0.57    inference(resolution,[],[f63,f80])).
% 0.20/0.57  fof(f63,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.57  fof(f713,plain,(
% 0.20/0.57    k1_xboole_0 != k1_tarski(sK0) | sK0 = sK1),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f705])).
% 0.20/0.57  fof(f705,plain,(
% 0.20/0.57    k1_xboole_0 != k1_tarski(sK0) | sK0 = sK1 | sK0 = sK1),
% 0.20/0.57    inference(superposition,[],[f49,f701])).
% 0.20/0.57  fof(f701,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f692])).
% 0.20/0.57  fof(f692,plain,(
% 0.20/0.57    k1_tarski(sK0) != k1_tarski(sK0) | sK0 = sK1 | k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.57    inference(superposition,[],[f49,f142])).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    ( ! [X2,X1] : (k1_tarski(X1) = k4_xboole_0(k1_tarski(X1),X2) | k1_xboole_0 = k4_xboole_0(k1_tarski(X1),X2)) )),
% 0.20/0.57    inference(resolution,[],[f69,f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.57    inference(flattening,[],[f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f819,plain,(
% 0.20/0.57    k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f720,f82])).
% 0.20/0.57  fof(f82,plain,(
% 0.20/0.57    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.20/0.57    inference(equality_resolution,[],[f71])).
% 0.20/0.57  fof(f71,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f46])).
% 0.20/0.57  fof(f720,plain,(
% 0.20/0.57    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.57    inference(backward_demodulation,[],[f109,f717])).
% 0.20/0.57  fof(f717,plain,(
% 0.20/0.57    sK0 = sK1),
% 0.20/0.57    inference(subsumption_resolution,[],[f712,f64])).
% 0.20/0.57  fof(f64,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.57    inference(ennf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.20/0.57  fof(f712,plain,(
% 0.20/0.57    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f710])).
% 0.20/0.57  fof(f710,plain,(
% 0.20/0.57    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.20/0.57    inference(superposition,[],[f72,f701])).
% 0.20/0.57  fof(f109,plain,(
% 0.20/0.57    ~r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f104,f64])).
% 0.20/0.57  fof(f104,plain,(
% 0.20/0.57    k1_xboole_0 = k1_tarski(sK0) | ~r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | sK0 != sK1),
% 0.20/0.57    inference(superposition,[],[f73,f48])).
% 0.20/0.57  fof(f73,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f47])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (25246)------------------------------
% 0.20/0.57  % (25246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (25246)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (25246)Memory used [KB]: 2558
% 0.20/0.57  % (25246)Time elapsed: 0.125 s
% 0.20/0.57  % (25246)------------------------------
% 0.20/0.57  % (25246)------------------------------
% 0.20/0.57  % (25234)Success in time 0.204 s
%------------------------------------------------------------------------------
