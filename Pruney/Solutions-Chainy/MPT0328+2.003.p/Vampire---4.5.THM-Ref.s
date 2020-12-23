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
% DateTime   : Thu Dec  3 12:42:57 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
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
fof(f561,plain,(
    $false ),
    inference(subsumption_resolution,[],[f547,f34])).

fof(f34,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & ~ r2_hidden(X0,X1) )
   => ( sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f547,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f487,f499])).

fof(f499,plain,(
    sK0 = sK2(sK1,k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f495,f54])).

fof(f54,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f495,plain,(
    r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f494,f487])).

fof(f494,plain,
    ( r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0))
    | ~ r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f488,f59])).

fof(f59,plain,(
    sK1 != k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f35,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f488,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK0))
    | r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0))
    | ~ r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(resolution,[],[f487,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f487,plain,(
    r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,
    ( r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1)
    | r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK2(sK1,k1_tarski(sK0),X0),sK1)
      | r2_hidden(sK2(sK1,k1_tarski(sK0),X0),X0) ) ),
    inference(superposition,[],[f59,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:45:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (9340)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (9337)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (9332)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (9323)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (9329)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (9348)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (9348)Refutation not found, incomplete strategy% (9348)------------------------------
% 0.22/0.54  % (9348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9322)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (9348)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9348)Memory used [KB]: 6268
% 0.22/0.54  % (9348)Time elapsed: 0.125 s
% 0.22/0.54  % (9348)------------------------------
% 0.22/0.54  % (9348)------------------------------
% 0.22/0.54  % (9327)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (9344)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (9334)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (9345)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (9325)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.55  % (9336)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (9336)Refutation not found, incomplete strategy% (9336)------------------------------
% 0.22/0.55  % (9336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9336)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9336)Memory used [KB]: 1663
% 0.22/0.55  % (9336)Time elapsed: 0.098 s
% 0.22/0.55  % (9336)------------------------------
% 0.22/0.55  % (9336)------------------------------
% 0.22/0.55  % (9330)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (9326)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (9335)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (9328)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (9338)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (9338)Refutation not found, incomplete strategy% (9338)------------------------------
% 0.22/0.56  % (9338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (9338)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (9338)Memory used [KB]: 10618
% 0.22/0.56  % (9338)Time elapsed: 0.144 s
% 0.22/0.56  % (9338)------------------------------
% 0.22/0.56  % (9338)------------------------------
% 0.22/0.56  % (9349)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.56  % (9323)Refutation not found, incomplete strategy% (9323)------------------------------
% 1.47/0.56  % (9323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (9323)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (9323)Memory used [KB]: 1663
% 1.47/0.56  % (9323)Time elapsed: 0.142 s
% 1.47/0.56  % (9323)------------------------------
% 1.47/0.56  % (9323)------------------------------
% 1.47/0.56  % (9350)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.47/0.56  % (9324)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.47/0.56  % (9346)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.56  % (9343)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.47/0.56  % (9333)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.47/0.57  % (9342)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.47/0.57  % (9341)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.47/0.57  % (9351)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.47/0.57  % (9339)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.57  % (9351)Refutation not found, incomplete strategy% (9351)------------------------------
% 1.47/0.57  % (9351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (9351)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (9351)Memory used [KB]: 1663
% 1.47/0.57  % (9351)Time elapsed: 0.157 s
% 1.47/0.57  % (9351)------------------------------
% 1.47/0.57  % (9351)------------------------------
% 1.47/0.57  % (9347)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.57  % (9331)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.47/0.58  % (9339)Refutation not found, incomplete strategy% (9339)------------------------------
% 1.47/0.58  % (9339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (9339)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (9339)Memory used [KB]: 1791
% 1.47/0.58  % (9339)Time elapsed: 0.169 s
% 1.47/0.58  % (9339)------------------------------
% 1.47/0.58  % (9339)------------------------------
% 1.66/0.60  % (9334)Refutation found. Thanks to Tanya!
% 1.66/0.60  % SZS status Theorem for theBenchmark
% 1.66/0.61  % SZS output start Proof for theBenchmark
% 1.66/0.61  fof(f561,plain,(
% 1.66/0.61    $false),
% 1.66/0.61    inference(subsumption_resolution,[],[f547,f34])).
% 1.66/0.61  fof(f34,plain,(
% 1.66/0.61    ~r2_hidden(sK0,sK1)),
% 1.66/0.61    inference(cnf_transformation,[],[f24])).
% 1.66/0.61  fof(f24,plain,(
% 1.66/0.61    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1)),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.66/0.61  fof(f23,plain,(
% 1.66/0.61    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1)) => (sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & ~r2_hidden(sK0,sK1))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f22,plain,(
% 1.66/0.61    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1))),
% 1.66/0.61    inference(ennf_transformation,[],[f21])).
% 1.66/0.61  fof(f21,negated_conjecture,(
% 1.66/0.61    ~! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.66/0.61    inference(negated_conjecture,[],[f20])).
% 1.66/0.61  fof(f20,conjecture,(
% 1.66/0.61    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 1.66/0.61  fof(f547,plain,(
% 1.66/0.61    r2_hidden(sK0,sK1)),
% 1.66/0.61    inference(superposition,[],[f487,f499])).
% 1.66/0.61  fof(f499,plain,(
% 1.66/0.61    sK0 = sK2(sK1,k1_tarski(sK0),sK1)),
% 1.66/0.61    inference(resolution,[],[f495,f54])).
% 1.66/0.61  fof(f54,plain,(
% 1.66/0.61    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.66/0.61    inference(equality_resolution,[],[f44])).
% 1.66/0.61  fof(f44,plain,(
% 1.66/0.61    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.66/0.61    inference(cnf_transformation,[],[f33])).
% 1.66/0.61  fof(f33,plain,(
% 1.66/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.66/0.61  fof(f32,plain,(
% 1.66/0.61    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f31,plain,(
% 1.66/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.61    inference(rectify,[],[f30])).
% 1.66/0.61  fof(f30,plain,(
% 1.66/0.61    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.66/0.61    inference(nnf_transformation,[],[f10])).
% 1.66/0.61  fof(f10,axiom,(
% 1.66/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.66/0.61  fof(f495,plain,(
% 1.66/0.61    r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f494,f487])).
% 1.66/0.61  fof(f494,plain,(
% 1.66/0.61    r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0)) | ~r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.66/0.61    inference(subsumption_resolution,[],[f488,f59])).
% 1.66/0.61  fof(f59,plain,(
% 1.66/0.61    sK1 != k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.66/0.61    inference(superposition,[],[f35,f36])).
% 1.66/0.61  fof(f36,plain,(
% 1.66/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f5])).
% 1.66/0.61  fof(f5,axiom,(
% 1.66/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.66/0.61  fof(f35,plain,(
% 1.66/0.61    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.66/0.61    inference(cnf_transformation,[],[f24])).
% 1.66/0.61  fof(f488,plain,(
% 1.66/0.61    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) | r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),k1_tarski(sK0)) | ~r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.66/0.61    inference(resolution,[],[f487,f43])).
% 1.66/0.61  fof(f43,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f29])).
% 1.66/0.61  fof(f29,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.66/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 1.66/0.61  fof(f28,plain,(
% 1.66/0.61    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.66/0.61    introduced(choice_axiom,[])).
% 1.66/0.61  fof(f27,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.66/0.61    inference(rectify,[],[f26])).
% 1.66/0.61  fof(f26,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.66/0.61    inference(flattening,[],[f25])).
% 1.66/0.61  fof(f25,plain,(
% 1.66/0.61    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.66/0.61    inference(nnf_transformation,[],[f2])).
% 1.66/0.61  fof(f2,axiom,(
% 1.66/0.61    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.66/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.66/0.61  fof(f487,plain,(
% 1.66/0.61    r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f486])).
% 1.66/0.61  fof(f486,plain,(
% 1.66/0.61    r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1) | r2_hidden(sK2(sK1,k1_tarski(sK0),sK1),sK1)),
% 1.66/0.61    inference(equality_resolution,[],[f74])).
% 1.66/0.61  fof(f74,plain,(
% 1.66/0.61    ( ! [X0] : (sK1 != X0 | r2_hidden(sK2(sK1,k1_tarski(sK0),X0),sK1) | r2_hidden(sK2(sK1,k1_tarski(sK0),X0),X0)) )),
% 1.66/0.61    inference(superposition,[],[f59,f41])).
% 1.66/0.61  fof(f41,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f29])).
% 1.66/0.61  % SZS output end Proof for theBenchmark
% 1.66/0.61  % (9334)------------------------------
% 1.66/0.61  % (9334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (9334)Termination reason: Refutation
% 1.66/0.61  
% 1.66/0.61  % (9334)Memory used [KB]: 11129
% 1.66/0.61  % (9334)Time elapsed: 0.190 s
% 1.66/0.61  % (9334)------------------------------
% 1.66/0.61  % (9334)------------------------------
% 1.66/0.61  % (9321)Success in time 0.24 s
%------------------------------------------------------------------------------
