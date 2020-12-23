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
% DateTime   : Thu Dec  3 12:42:57 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   34 (  92 expanded)
%              Number of leaves         :    7 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  157 ( 451 expanded)
%              Number of equality atoms :   51 ( 118 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(subsumption_resolution,[],[f545,f32])).

fof(f32,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f545,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f485,f497])).

fof(f497,plain,(
    sK0 = sK3(sK1,k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f493,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f493,plain,(
    r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f492,f485])).

fof(f492,plain,
    ( r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0))
    | ~ r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f486,f57])).

fof(f57,plain,(
    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f33,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f486,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0))
    | ~ r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(resolution,[],[f485,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f485,plain,(
    r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f484])).

fof(f484,plain,
    ( r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1)
    | r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(sK1,k1_tarski(sK0),X0),sK1)
      | r2_hidden(sK3(sK1,k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f57,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:52:34 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (30340)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.50  % (30340)Refutation not found, incomplete strategy% (30340)------------------------------
% 0.22/0.50  % (30340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (30340)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (30340)Memory used [KB]: 1663
% 0.22/0.50  % (30340)Time elapsed: 0.069 s
% 0.22/0.50  % (30340)------------------------------
% 0.22/0.50  % (30340)------------------------------
% 0.22/0.53  % (30342)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (30359)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (30351)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (30366)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.57  % (30348)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.57  % (30344)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (30341)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.57/0.58  % (30363)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.57/0.59  % (30361)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.57/0.59  % (30356)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.57/0.59  % (30347)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.57/0.59  % (30343)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.59  % (30339)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.78/0.59  % (30353)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.78/0.60  % (30353)Refutation not found, incomplete strategy% (30353)------------------------------
% 1.78/0.60  % (30353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (30353)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.60  
% 1.78/0.60  % (30353)Memory used [KB]: 1663
% 1.78/0.60  % (30353)Time elapsed: 0.162 s
% 1.78/0.60  % (30353)------------------------------
% 1.78/0.60  % (30353)------------------------------
% 1.78/0.60  % (30362)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.78/0.60  % (30367)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.78/0.61  % (30355)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.78/0.61  % (30355)Refutation not found, incomplete strategy% (30355)------------------------------
% 1.78/0.61  % (30355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (30355)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (30355)Memory used [KB]: 10618
% 1.78/0.61  % (30355)Time elapsed: 0.151 s
% 1.78/0.61  % (30355)------------------------------
% 1.78/0.61  % (30355)------------------------------
% 1.78/0.61  % (30358)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.78/0.61  % (30356)Refutation not found, incomplete strategy% (30356)------------------------------
% 1.78/0.61  % (30356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (30356)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (30356)Memory used [KB]: 1791
% 1.78/0.61  % (30356)Time elapsed: 0.185 s
% 1.78/0.61  % (30356)------------------------------
% 1.78/0.61  % (30356)------------------------------
% 1.78/0.61  % (30345)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.78/0.61  % (30357)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.78/0.61  % (30360)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.78/0.61  % (30342)Refutation not found, incomplete strategy% (30342)------------------------------
% 1.78/0.61  % (30342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (30342)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (30342)Memory used [KB]: 6140
% 1.78/0.61  % (30342)Time elapsed: 0.186 s
% 1.78/0.61  % (30342)------------------------------
% 1.78/0.61  % (30342)------------------------------
% 1.78/0.61  % (30350)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.78/0.62  % (30364)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.78/0.62  % (30352)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.78/0.62  % (30349)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.78/0.63  % (30365)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.78/0.63  % (30365)Refutation not found, incomplete strategy% (30365)------------------------------
% 1.78/0.63  % (30365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.63  % (30365)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.63  
% 1.78/0.63  % (30365)Memory used [KB]: 6140
% 1.78/0.63  % (30365)Time elapsed: 0.191 s
% 1.78/0.63  % (30365)------------------------------
% 1.78/0.63  % (30365)------------------------------
% 1.78/0.63  % (30346)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.78/0.63  % (30368)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.78/0.63  % (30368)Refutation not found, incomplete strategy% (30368)------------------------------
% 1.78/0.63  % (30368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.63  % (30368)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.63  
% 1.78/0.63  % (30368)Memory used [KB]: 1663
% 1.78/0.63  % (30368)Time elapsed: 0.203 s
% 1.78/0.63  % (30368)------------------------------
% 1.78/0.63  % (30368)------------------------------
% 1.78/0.64  % (30351)Refutation found. Thanks to Tanya!
% 1.78/0.64  % SZS status Theorem for theBenchmark
% 1.78/0.64  % SZS output start Proof for theBenchmark
% 1.78/0.64  fof(f559,plain,(
% 1.78/0.64    $false),
% 1.78/0.64    inference(subsumption_resolution,[],[f545,f32])).
% 1.78/0.64  fof(f32,plain,(
% 1.78/0.64    ~r2_hidden(sK0,sK1)),
% 1.78/0.64    inference(cnf_transformation,[],[f22])).
% 1.78/0.64  fof(f22,plain,(
% 1.78/0.64    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1)),
% 1.78/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f21])).
% 1.78/0.64  fof(f21,plain,(
% 1.78/0.64    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1)) => (sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1))),
% 1.78/0.64    introduced(choice_axiom,[])).
% 1.78/0.64  fof(f20,plain,(
% 1.78/0.64    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1))),
% 1.78/0.64    inference(ennf_transformation,[],[f19])).
% 1.78/0.64  fof(f19,negated_conjecture,(
% 1.78/0.64    ~! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.78/0.64    inference(negated_conjecture,[],[f18])).
% 1.78/0.64  fof(f18,conjecture,(
% 1.78/0.64    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.78/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 1.78/0.64  fof(f545,plain,(
% 1.78/0.64    r2_hidden(sK0,sK1)),
% 1.78/0.64    inference(superposition,[],[f485,f497])).
% 1.78/0.64  fof(f497,plain,(
% 1.78/0.64    sK0 = sK3(sK1,k1_tarski(sK0),sK1)),
% 1.78/0.64    inference(resolution,[],[f493,f49])).
% 1.78/0.64  fof(f49,plain,(
% 1.78/0.64    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.78/0.64    inference(equality_resolution,[],[f35])).
% 1.78/0.64  fof(f35,plain,(
% 1.78/0.64    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.78/0.64    inference(cnf_transformation,[],[f26])).
% 1.78/0.64  fof(f26,plain,(
% 1.78/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.78/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.78/0.64  fof(f25,plain,(
% 1.78/0.64    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.78/0.64    introduced(choice_axiom,[])).
% 1.78/0.64  fof(f24,plain,(
% 1.78/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.78/0.64    inference(rectify,[],[f23])).
% 1.78/0.64  fof(f23,plain,(
% 1.78/0.64    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.78/0.64    inference(nnf_transformation,[],[f9])).
% 1.78/0.64  fof(f9,axiom,(
% 1.78/0.64    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.78/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.78/0.64  fof(f493,plain,(
% 1.78/0.64    r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 1.78/0.64    inference(subsumption_resolution,[],[f492,f485])).
% 1.78/0.64  fof(f492,plain,(
% 1.78/0.64    r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0)) | ~r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.78/0.64    inference(subsumption_resolution,[],[f486,f57])).
% 1.78/0.64  fof(f57,plain,(
% 1.78/0.64    sK1 != k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.78/0.64    inference(superposition,[],[f33,f34])).
% 1.78/0.64  fof(f34,plain,(
% 1.78/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f3])).
% 1.78/0.64  fof(f3,axiom,(
% 1.78/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.78/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.78/0.64  fof(f33,plain,(
% 1.78/0.64    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.78/0.64    inference(cnf_transformation,[],[f22])).
% 1.78/0.64  fof(f486,plain,(
% 1.78/0.64    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) | r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0)) | ~r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.78/0.64    inference(resolution,[],[f485,f45])).
% 1.78/0.64  fof(f45,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f31])).
% 1.78/0.64  fof(f31,plain,(
% 1.78/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.78/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.78/0.64  fof(f30,plain,(
% 1.78/0.64    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.78/0.64    introduced(choice_axiom,[])).
% 1.78/0.64  fof(f29,plain,(
% 1.78/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.78/0.64    inference(rectify,[],[f28])).
% 1.78/0.64  fof(f28,plain,(
% 1.78/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.78/0.64    inference(flattening,[],[f27])).
% 1.78/0.64  fof(f27,plain,(
% 1.78/0.64    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.78/0.64    inference(nnf_transformation,[],[f1])).
% 1.78/0.64  fof(f1,axiom,(
% 1.78/0.64    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.78/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.78/0.64  fof(f485,plain,(
% 1.78/0.64    r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.78/0.64    inference(duplicate_literal_removal,[],[f484])).
% 1.78/0.64  fof(f484,plain,(
% 1.78/0.64    r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1) | r2_hidden(sK3(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.78/0.64    inference(equality_resolution,[],[f72])).
% 1.78/0.64  fof(f72,plain,(
% 1.78/0.64    ( ! [X0] : (sK1 != X0 | r2_hidden(sK3(sK1,k1_tarski(sK0),X0),sK1) | r2_hidden(sK3(sK1,k1_tarski(sK0),X0),X0)) )),
% 1.78/0.64    inference(superposition,[],[f57,f43])).
% 1.78/0.64  fof(f43,plain,(
% 1.78/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.78/0.64    inference(cnf_transformation,[],[f31])).
% 1.78/0.64  % SZS output end Proof for theBenchmark
% 1.78/0.64  % (30351)------------------------------
% 1.78/0.64  % (30351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.64  % (30351)Termination reason: Refutation
% 1.78/0.64  
% 1.78/0.64  % (30351)Memory used [KB]: 11129
% 1.78/0.64  % (30351)Time elapsed: 0.213 s
% 1.78/0.64  % (30351)------------------------------
% 1.78/0.64  % (30351)------------------------------
% 2.22/0.65  % (30354)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.22/0.66  % (30338)Success in time 0.283 s
%------------------------------------------------------------------------------
