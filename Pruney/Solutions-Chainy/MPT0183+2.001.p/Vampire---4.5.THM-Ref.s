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
% DateTime   : Thu Dec  3 12:34:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f131,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( sK0 != sK0
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f34,f108])).

fof(f108,plain,(
    sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f103,f27])).

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

fof(f103,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( sK1 != sK1
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f32,f79])).

fof(f79,plain,
    ( sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f76,f25])).

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

fof(f76,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f60])).

fof(f60,plain,
    ( sK2 != sK2
    | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f33,f52])).

fof(f52,plain,
    ( sK2 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) ),
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
    ( sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK2 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))
    | r2_hidden(sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_enumset1(sK0,sK1,sK2) != X0
      | sK0 = sK3(sK1,sK2,sK0,X0)
      | sK2 = sK3(sK1,sK2,sK0,X0)
      | sK1 = sK3(sK1,sK2,sK0,X0)
      | r2_hidden(sK3(sK1,sK2,sK0,X0),X0) ) ),
    inference(superposition,[],[f14,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).

% (27401)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (27402)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (27395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (27402)Refutation not found, incomplete strategy% (27402)------------------------------
% (27402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27393)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (27411)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (27403)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (27390)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (27404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (27392)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (27390)Refutation not found, incomplete strategy% (27390)------------------------------
% (27390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27390)Termination reason: Refutation not found, incomplete strategy

% (27390)Memory used [KB]: 10618
% (27390)Time elapsed: 0.150 s
% (27390)------------------------------
% (27390)------------------------------
% (27386)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (27392)Refutation not found, incomplete strategy% (27392)------------------------------
% (27392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27392)Termination reason: Refutation not found, incomplete strategy

% (27392)Memory used [KB]: 10618
% (27392)Time elapsed: 0.148 s
% (27392)------------------------------
% (27392)------------------------------
% (27386)Refutation not found, incomplete strategy% (27386)------------------------------
% (27386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27386)Termination reason: Refutation not found, incomplete strategy

% (27386)Memory used [KB]: 6140
% (27386)Time elapsed: 0.126 s
% (27386)------------------------------
% (27386)------------------------------
% (27408)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f14,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f33,plain,(
    ! [X2] :
      ( sK2 != sK3(sK1,sK2,sK0,X2)
      | k1_enumset1(sK0,sK1,sK2) != X2
      | ~ r2_hidden(sK3(sK1,sK2,sK0,X2),X2) ) ),
    inference(superposition,[],[f14,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X1
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X1] :
      ( sK1 != sK3(sK1,sK2,sK0,X1)
      | k1_enumset1(sK0,sK1,sK2) != X1
      | ~ r2_hidden(sK3(sK1,sK2,sK0,X1),X1) ) ),
    inference(superposition,[],[f14,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X3] :
      ( sK0 != sK3(sK1,sK2,sK0,X3)
      | k1_enumset1(sK0,sK1,sK2) != X3
      | ~ r2_hidden(sK3(sK1,sK2,sK0,X3),X3) ) ),
    inference(superposition,[],[f14,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X2
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (27391)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (27387)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (27399)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.52  % (27407)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (27407)Refutation not found, incomplete strategy% (27407)------------------------------
% 0.20/0.53  % (27407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27399)Refutation not found, incomplete strategy% (27399)------------------------------
% 0.20/0.53  % (27399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27399)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27399)Memory used [KB]: 10618
% 0.20/0.53  % (27399)Time elapsed: 0.116 s
% 0.20/0.53  % (27399)------------------------------
% 0.20/0.53  % (27399)------------------------------
% 0.20/0.53  % (27383)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (27407)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27407)Memory used [KB]: 6268
% 0.20/0.53  % (27407)Time elapsed: 0.117 s
% 0.20/0.53  % (27407)------------------------------
% 0.20/0.53  % (27407)------------------------------
% 0.20/0.53  % (27391)Refutation not found, incomplete strategy% (27391)------------------------------
% 0.20/0.53  % (27391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27391)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27391)Memory used [KB]: 10618
% 0.20/0.53  % (27391)Time elapsed: 0.116 s
% 0.20/0.53  % (27391)------------------------------
% 0.20/0.53  % (27391)------------------------------
% 0.20/0.53  % (27397)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (27384)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (27397)Refutation not found, incomplete strategy% (27397)------------------------------
% 0.20/0.53  % (27397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27397)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27397)Memory used [KB]: 6140
% 0.20/0.53  % (27397)Time elapsed: 0.081 s
% 0.20/0.53  % (27397)------------------------------
% 0.20/0.53  % (27397)------------------------------
% 0.20/0.53  % (27384)Refutation not found, incomplete strategy% (27384)------------------------------
% 0.20/0.53  % (27384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27384)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27384)Memory used [KB]: 10618
% 0.20/0.53  % (27384)Time elapsed: 0.114 s
% 0.20/0.53  % (27384)------------------------------
% 0.20/0.53  % (27384)------------------------------
% 0.20/0.53  % (27385)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (27382)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (27382)Refutation not found, incomplete strategy% (27382)------------------------------
% 0.20/0.54  % (27382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (27382)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (27382)Memory used [KB]: 1663
% 0.20/0.54  % (27382)Time elapsed: 0.083 s
% 0.20/0.54  % (27382)------------------------------
% 0.20/0.54  % (27382)------------------------------
% 0.20/0.54  % (27410)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (27406)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (27388)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (27389)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (27409)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (27400)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (27396)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (27405)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (27398)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (27405)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f131,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.55    inference(rectify,[],[f10])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.55    inference(flattening,[],[f9])).
% 0.20/0.55  fof(f9,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.20/0.55    inference(nnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,plain,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.20/0.55    inference(ennf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 0.20/0.55  fof(f131,plain,(
% 0.20/0.55    ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    sK0 != sK0 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | ~r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(superposition,[],[f34,f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f103,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X2,X0,X5] : (r2_hidden(X5,k1_enumset1(X0,X5,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k1_enumset1(X0,X5,X2) != X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    sK1 != sK1 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | ~r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(superposition,[],[f32,f79])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f76,f25])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 0.20/0.55    inference(equality_resolution,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 0.20/0.55    inference(equality_resolution,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    sK2 != sK2 | k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK0,sK1,sK2) | ~r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(superposition,[],[f33,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    sK2 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(subsumption_resolution,[],[f51,f30])).
% 0.20/0.55  fof(f30,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k1_enumset1(X0,X1,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    sK0 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK2 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | sK1 = sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)) | r2_hidden(sK3(sK1,sK2,sK0,k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))),
% 0.20/0.55    inference(equality_resolution,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X0] : (k1_enumset1(sK0,sK1,sK2) != X0 | sK0 = sK3(sK1,sK2,sK0,X0) | sK2 = sK3(sK1,sK2,sK0,X0) | sK1 = sK3(sK1,sK2,sK0,X0) | r2_hidden(sK3(sK1,sK2,sK0,X0),X0)) )),
% 0.20/0.55    inference(superposition,[],[f14,f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  % (27401)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (27402)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (27395)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (27402)Refutation not found, incomplete strategy% (27402)------------------------------
% 0.20/0.55  % (27402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (27393)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (27411)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (27403)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (27390)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (27404)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (27392)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.56  % (27390)Refutation not found, incomplete strategy% (27390)------------------------------
% 0.20/0.56  % (27390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27390)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (27390)Memory used [KB]: 10618
% 0.20/0.56  % (27390)Time elapsed: 0.150 s
% 0.20/0.56  % (27390)------------------------------
% 0.20/0.56  % (27390)------------------------------
% 0.20/0.56  % (27386)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (27392)Refutation not found, incomplete strategy% (27392)------------------------------
% 0.20/0.56  % (27392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27392)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (27392)Memory used [KB]: 10618
% 0.20/0.56  % (27392)Time elapsed: 0.148 s
% 0.20/0.56  % (27392)------------------------------
% 0.20/0.56  % (27392)------------------------------
% 0.20/0.56  % (27386)Refutation not found, incomplete strategy% (27386)------------------------------
% 0.20/0.56  % (27386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27386)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (27386)Memory used [KB]: 6140
% 0.20/0.56  % (27386)Time elapsed: 0.126 s
% 0.20/0.56  % (27386)------------------------------
% 0.20/0.56  % (27386)------------------------------
% 0.20/0.56  % (27408)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,plain,(
% 0.20/0.56    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f7])).
% 0.20/0.56  fof(f7,plain,(
% 0.20/0.56    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK2,sK0)),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f5,plain,(
% 0.20/0.56    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X2,X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.20/0.56    inference(negated_conjecture,[],[f3])).
% 0.20/0.56  fof(f3,conjecture,(
% 0.20/0.56    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ( ! [X2] : (sK2 != sK3(sK1,sK2,sK0,X2) | k1_enumset1(sK0,sK1,sK2) != X2 | ~r2_hidden(sK3(sK1,sK2,sK0,X2),X2)) )),
% 0.20/0.56    inference(superposition,[],[f14,f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X1 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X1] : (sK1 != sK3(sK1,sK2,sK0,X1) | k1_enumset1(sK0,sK1,sK2) != X1 | ~r2_hidden(sK3(sK1,sK2,sK0,X1),X1)) )),
% 0.20/0.56    inference(superposition,[],[f14,f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ( ! [X3] : (sK0 != sK3(sK1,sK2,sK0,X3) | k1_enumset1(sK0,sK1,sK2) != X3 | ~r2_hidden(sK3(sK1,sK2,sK0,X3),X3)) )),
% 0.20/0.56    inference(superposition,[],[f14,f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X2 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (27405)------------------------------
% 0.20/0.56  % (27405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (27405)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (27405)Memory used [KB]: 1791
% 0.20/0.56  % (27405)Time elapsed: 0.102 s
% 0.20/0.56  % (27405)------------------------------
% 0.20/0.56  % (27405)------------------------------
% 0.20/0.56  % (27381)Success in time 0.194 s
%------------------------------------------------------------------------------
