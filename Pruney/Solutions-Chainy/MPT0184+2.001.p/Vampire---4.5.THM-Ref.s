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
% DateTime   : Thu Dec  3 12:34:13 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 110 expanded)
%              Number of leaves         :    4 (  24 expanded)
%              Depth                    :   18
%              Number of atoms          :  189 ( 896 expanded)
%              Number of equality atoms :  140 ( 693 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f132,plain,(
    $false ),
    inference(subsumption_resolution,[],[f131,f29])).

fof(f29,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).

fof(f12,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f131,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f34,f108])).

% (9514)Refutation not found, incomplete strategy% (9514)------------------------------
% (9514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9502)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (9514)Termination reason: Refutation not found, incomplete strategy

% (9514)Memory used [KB]: 10618
% (9514)Time elapsed: 0.133 s
% (9514)------------------------------
% (9514)------------------------------
% (9503)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (9503)Refutation not found, incomplete strategy% (9503)------------------------------
% (9503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9503)Termination reason: Refutation not found, incomplete strategy

% (9503)Memory used [KB]: 10618
% (9503)Time elapsed: 0.148 s
% (9503)------------------------------
% (9503)------------------------------
% (9507)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (9518)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (9509)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (9507)Refutation not found, incomplete strategy% (9507)------------------------------
% (9507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9507)Termination reason: Refutation not found, incomplete strategy

% (9507)Memory used [KB]: 6140
% (9507)Time elapsed: 0.149 s
% (9507)------------------------------
% (9507)------------------------------
% (9509)Refutation not found, incomplete strategy% (9509)------------------------------
% (9509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9517)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (9510)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f108,plain,(
    sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f105,f27])).

% (9508)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f27,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( sK1 != sK1
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f33,f80])).

fof(f80,plain,
    ( sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f75,f25])).

fof(f25,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( sK2 != sK2
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f32,f52])).

fof(f52,plain,
    ( sK2 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f51,f30])).

fof(f30,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK2 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_enumset1(sK0,sK1,sK2) != X0
      | sK0 = sK3(sK2,sK1,sK0,X0)
      | sK1 = sK3(sK2,sK1,sK0,X0)
      | sK2 = sK3(sK2,sK1,sK0,X0)
      | r2_hidden(sK3(sK2,sK1,sK0,X0),X0) ) ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(f32,plain,(
    ! [X1] :
      ( sK2 != sK3(sK2,sK1,sK0,X1)
      | k1_enumset1(sK0,sK1,sK2) != X1
      | ~ r2_hidden(sK3(sK2,sK1,sK0,X1),X1) ) ),
    inference(superposition,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X2] :
      ( sK1 != sK3(sK2,sK1,sK0,X2)
      | k1_enumset1(sK0,sK1,sK2) != X2
      | ~ r2_hidden(sK3(sK2,sK1,sK0,X2),X2) ) ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X3] :
      ( sK0 != sK3(sK2,sK1,sK0,X3)
      | k1_enumset1(sK0,sK1,sK2) != X3
      | ~ r2_hidden(sK3(sK2,sK1,sK0,X3),X3) ) ),
    inference(superposition,[],[f14,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:29:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (9504)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (9501)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (9501)Refutation not found, incomplete strategy% (9501)------------------------------
% 0.22/0.54  % (9501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9501)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (9501)Memory used [KB]: 10618
% 0.22/0.54  % (9501)Time elapsed: 0.125 s
% 0.22/0.54  % (9501)------------------------------
% 0.22/0.54  % (9501)------------------------------
% 0.22/0.54  % (9514)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (9512)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (9513)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (9500)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (9520)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (9500)Refutation not found, incomplete strategy% (9500)------------------------------
% 0.22/0.55  % (9500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (9500)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (9500)Memory used [KB]: 10618
% 0.22/0.55  % (9500)Time elapsed: 0.128 s
% 0.22/0.55  % (9500)------------------------------
% 0.22/0.55  % (9500)------------------------------
% 1.41/0.55  % (9519)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.55  % (9492)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.55  % (9513)Refutation not found, incomplete strategy% (9513)------------------------------
% 1.41/0.55  % (9513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9513)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9513)Memory used [KB]: 1663
% 1.41/0.55  % (9513)Time elapsed: 0.088 s
% 1.41/0.55  % (9513)------------------------------
% 1.41/0.55  % (9513)------------------------------
% 1.41/0.55  % (9492)Refutation not found, incomplete strategy% (9492)------------------------------
% 1.41/0.55  % (9492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9492)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9492)Memory used [KB]: 1663
% 1.41/0.55  % (9492)Time elapsed: 0.133 s
% 1.41/0.55  % (9492)------------------------------
% 1.41/0.55  % (9492)------------------------------
% 1.41/0.55  % (9496)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.55  % (9496)Refutation not found, incomplete strategy% (9496)------------------------------
% 1.41/0.55  % (9496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9496)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9496)Memory used [KB]: 6140
% 1.41/0.55  % (9496)Time elapsed: 0.135 s
% 1.41/0.55  % (9496)------------------------------
% 1.41/0.55  % (9496)------------------------------
% 1.41/0.55  % (9516)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.55  % (9506)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.55  % (9497)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.55  % (9499)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (9505)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.55  % (9498)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.55  % (9493)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.55  % (9494)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.55  % (9512)Refutation not found, incomplete strategy% (9512)------------------------------
% 1.41/0.55  % (9512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9512)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9512)Memory used [KB]: 10618
% 1.41/0.55  % (9512)Time elapsed: 0.128 s
% 1.41/0.55  % (9512)------------------------------
% 1.41/0.55  % (9512)------------------------------
% 1.41/0.55  % (9494)Refutation not found, incomplete strategy% (9494)------------------------------
% 1.41/0.55  % (9494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9494)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9494)Memory used [KB]: 10618
% 1.41/0.55  % (9494)Time elapsed: 0.136 s
% 1.41/0.55  % (9494)------------------------------
% 1.41/0.55  % (9494)------------------------------
% 1.41/0.55  % (9521)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.56  % (9495)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.56  % (9515)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.56  % (9511)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.56  % (9515)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f132,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(subsumption_resolution,[],[f131,f29])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 1.41/0.56    inference(equality_resolution,[],[f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 1.41/0.56    inference(equality_resolution,[],[f17])).
% 1.41/0.56  fof(f17,plain,(
% 1.41/0.56    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.56    inference(cnf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,plain,(
% 1.41/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).
% 1.41/0.56  fof(f12,plain,(
% 1.41/0.56    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f11,plain,(
% 1.41/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.56    inference(rectify,[],[f10])).
% 1.41/0.56  fof(f10,plain,(
% 1.41/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.56    inference(flattening,[],[f9])).
% 1.41/0.56  fof(f9,plain,(
% 1.41/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.56    inference(nnf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,plain,(
% 1.41/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.41/0.56    inference(ennf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.41/0.56  fof(f131,plain,(
% 1.41/0.56    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.41/0.56    inference(trivial_inequality_removal,[],[f115])).
% 1.41/0.56  fof(f115,plain,(
% 1.41/0.56    sK0 != sK0 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.41/0.56    inference(superposition,[],[f34,f108])).
% 1.41/0.56  % (9514)Refutation not found, incomplete strategy% (9514)------------------------------
% 1.41/0.56  % (9514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (9502)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.56  % (9514)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (9514)Memory used [KB]: 10618
% 1.41/0.56  % (9514)Time elapsed: 0.133 s
% 1.41/0.56  % (9514)------------------------------
% 1.41/0.56  % (9514)------------------------------
% 1.41/0.56  % (9503)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.60/0.56  % (9503)Refutation not found, incomplete strategy% (9503)------------------------------
% 1.60/0.56  % (9503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.56  % (9503)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.56  
% 1.60/0.56  % (9503)Memory used [KB]: 10618
% 1.60/0.56  % (9503)Time elapsed: 0.148 s
% 1.60/0.56  % (9503)------------------------------
% 1.60/0.56  % (9503)------------------------------
% 1.60/0.56  % (9507)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.60/0.57  % (9518)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.60/0.57  % (9509)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.60/0.57  % (9507)Refutation not found, incomplete strategy% (9507)------------------------------
% 1.60/0.57  % (9507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (9507)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.57  
% 1.60/0.57  % (9507)Memory used [KB]: 6140
% 1.60/0.57  % (9507)Time elapsed: 0.149 s
% 1.60/0.57  % (9507)------------------------------
% 1.60/0.57  % (9507)------------------------------
% 1.60/0.57  % (9509)Refutation not found, incomplete strategy% (9509)------------------------------
% 1.60/0.57  % (9509)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (9517)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.60/0.57  % (9510)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.60/0.57  fof(f108,plain,(
% 1.60/0.57    sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.57    inference(subsumption_resolution,[],[f105,f27])).
% 1.60/0.58  % (9508)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.60/0.58  fof(f27,plain,(
% 1.60/0.58    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 1.60/0.58    inference(equality_resolution,[],[f26])).
% 1.60/0.58  fof(f26,plain,(
% 1.60/0.58    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 1.60/0.58    inference(equality_resolution,[],[f18])).
% 1.60/0.58  fof(f18,plain,(
% 1.60/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f105,plain,(
% 1.60/0.58    ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f90])).
% 1.60/0.58  fof(f90,plain,(
% 1.60/0.58    sK1 != sK1 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(superposition,[],[f33,f80])).
% 1.60/0.58  fof(f80,plain,(
% 1.60/0.58    sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f75,f25])).
% 1.60/0.58  fof(f25,plain,(
% 1.60/0.58    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.60/0.58    inference(equality_resolution,[],[f24])).
% 1.60/0.58  fof(f24,plain,(
% 1.60/0.58    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.60/0.58    inference(equality_resolution,[],[f19])).
% 1.60/0.58  fof(f19,plain,(
% 1.60/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f75,plain,(
% 1.60/0.58    ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(trivial_inequality_removal,[],[f61])).
% 1.60/0.58  fof(f61,plain,(
% 1.60/0.58    sK2 != sK2 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(superposition,[],[f32,f52])).
% 1.60/0.58  fof(f52,plain,(
% 1.60/0.58    sK2 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(subsumption_resolution,[],[f51,f30])).
% 1.60/0.58  fof(f30,plain,(
% 1.60/0.58    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 1.60/0.58    inference(equality_resolution,[],[f16])).
% 1.60/0.58  fof(f16,plain,(
% 1.60/0.58    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f51,plain,(
% 1.60/0.58    sK0 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | sK2 = sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK3(sK2,sK1,sK0,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),
% 1.60/0.58    inference(equality_resolution,[],[f31])).
% 1.60/0.58  fof(f31,plain,(
% 1.60/0.58    ( ! [X0] : (k1_enumset1(sK0,sK1,sK2) != X0 | sK0 = sK3(sK2,sK1,sK0,X0) | sK1 = sK3(sK2,sK1,sK0,X0) | sK2 = sK3(sK2,sK1,sK0,X0) | r2_hidden(sK3(sK2,sK1,sK0,X0),X0)) )),
% 1.60/0.58    inference(superposition,[],[f14,f20])).
% 1.60/0.58  fof(f20,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f14,plain,(
% 1.60/0.58    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0)),
% 1.60/0.58    inference(cnf_transformation,[],[f8])).
% 1.60/0.58  fof(f8,plain,(
% 1.60/0.58    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0)),
% 1.60/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).
% 1.60/0.58  fof(f7,plain,(
% 1.60/0.58    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK2,sK1,sK0)),
% 1.60/0.58    introduced(choice_axiom,[])).
% 1.60/0.58  fof(f5,plain,(
% 1.60/0.58    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X2,X1,X0)),
% 1.60/0.58    inference(ennf_transformation,[],[f4])).
% 1.60/0.58  fof(f4,negated_conjecture,(
% 1.60/0.58    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.60/0.58    inference(negated_conjecture,[],[f3])).
% 1.60/0.58  fof(f3,conjecture,(
% 1.60/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.60/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).
% 1.60/0.58  fof(f32,plain,(
% 1.60/0.58    ( ! [X1] : (sK2 != sK3(sK2,sK1,sK0,X1) | k1_enumset1(sK0,sK1,sK2) != X1 | ~r2_hidden(sK3(sK2,sK1,sK0,X1),X1)) )),
% 1.60/0.58    inference(superposition,[],[f14,f21])).
% 1.60/0.58  fof(f21,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f33,plain,(
% 1.60/0.58    ( ! [X2] : (sK1 != sK3(sK2,sK1,sK0,X2) | k1_enumset1(sK0,sK1,sK2) != X2 | ~r2_hidden(sK3(sK2,sK1,sK0,X2),X2)) )),
% 1.60/0.58    inference(superposition,[],[f14,f22])).
% 1.60/0.58  fof(f22,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X1 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  fof(f34,plain,(
% 1.60/0.58    ( ! [X3] : (sK0 != sK3(sK2,sK1,sK0,X3) | k1_enumset1(sK0,sK1,sK2) != X3 | ~r2_hidden(sK3(sK2,sK1,sK0,X3),X3)) )),
% 1.60/0.58    inference(superposition,[],[f14,f23])).
% 1.60/0.58  fof(f23,plain,(
% 1.60/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X2 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 1.60/0.58    inference(cnf_transformation,[],[f13])).
% 1.60/0.58  % SZS output end Proof for theBenchmark
% 1.60/0.58  % (9509)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (9509)Memory used [KB]: 10618
% 1.60/0.58  % (9509)Time elapsed: 0.161 s
% 1.60/0.58  % (9509)------------------------------
% 1.60/0.58  % (9509)------------------------------
% 1.60/0.58  % (9515)------------------------------
% 1.60/0.58  % (9515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (9515)Termination reason: Refutation
% 1.60/0.58  
% 1.60/0.58  % (9515)Memory used [KB]: 1791
% 1.60/0.58  % (9515)Time elapsed: 0.152 s
% 1.60/0.58  % (9515)------------------------------
% 1.60/0.58  % (9515)------------------------------
% 1.60/0.58  % (9491)Success in time 0.205 s
%------------------------------------------------------------------------------
