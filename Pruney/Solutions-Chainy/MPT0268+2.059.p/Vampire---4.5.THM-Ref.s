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
% DateTime   : Thu Dec  3 12:40:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 113 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   18
%              Number of atoms          :  229 ( 663 expanded)
%              Number of equality atoms :   64 ( 173 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f285,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f63,f254,f284])).

fof(f284,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f277,f52])).

fof(f52,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f277,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f272,f61])).

fof(f61,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f272,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k1_tarski(sK1)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f49,f56])).

fof(f56,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f254,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f252,f52])).

fof(f252,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f251,f57])).

fof(f57,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f251,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f229,f60])).

fof(f60,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f229,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl4_1 ),
    inference(superposition,[],[f39,f189])).

fof(f189,plain,
    ( sK1 = sK2(sK0,k1_tarski(sK1),sK0)
    | spl4_1 ),
    inference(resolution,[],[f155,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f155,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f154,f147])).

fof(f147,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0)
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0) )
    | spl4_1 ),
    inference(superposition,[],[f57,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f148,f57])).

fof(f148,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(resolution,[],[f147,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f33,f59,f55])).

fof(f33,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f62,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f34,f59,f55])).

fof(f34,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:39:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.52  % (30372)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.53  % (30380)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.53  % (30388)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.53  % (30364)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.54  % (30368)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (30365)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.54  % (30380)Refutation not found, incomplete strategy% (30380)------------------------------
% 0.23/0.54  % (30380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (30380)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (30380)Memory used [KB]: 10618
% 0.23/0.54  % (30380)Time elapsed: 0.114 s
% 0.23/0.54  % (30380)------------------------------
% 0.23/0.54  % (30380)------------------------------
% 0.23/0.54  % (30365)Refutation not found, incomplete strategy% (30365)------------------------------
% 0.23/0.54  % (30365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (30365)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (30365)Memory used [KB]: 1663
% 0.23/0.54  % (30365)Time elapsed: 0.092 s
% 0.23/0.54  % (30365)------------------------------
% 0.23/0.54  % (30365)------------------------------
% 0.23/0.54  % (30370)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.54  % (30387)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.55  % (30369)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.55  % (30366)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.55  % (30367)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.55  % (30392)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.55  % (30386)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.55  % (30379)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.55  % (30374)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.23/0.55  % (30375)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.55  % (30375)Refutation not found, incomplete strategy% (30375)------------------------------
% 0.23/0.55  % (30375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (30375)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (30375)Memory used [KB]: 6140
% 0.23/0.55  % (30375)Time elapsed: 0.133 s
% 0.23/0.55  % (30375)------------------------------
% 0.23/0.55  % (30375)------------------------------
% 0.23/0.55  % (30384)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.56  % (30385)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.56  % (30391)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.56  % (30371)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.56  % (30376)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.23/0.56  % (30390)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.56  % (30377)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.56  % (30378)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.56  % (30390)Refutation not found, incomplete strategy% (30390)------------------------------
% 0.23/0.56  % (30390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (30390)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (30390)Memory used [KB]: 6140
% 0.23/0.56  % (30390)Time elapsed: 0.147 s
% 0.23/0.56  % (30390)------------------------------
% 0.23/0.56  % (30390)------------------------------
% 0.23/0.56  % (30378)Refutation not found, incomplete strategy% (30378)------------------------------
% 0.23/0.56  % (30378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (30378)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.56  
% 0.23/0.56  % (30378)Memory used [KB]: 1663
% 0.23/0.56  % (30378)Time elapsed: 0.149 s
% 0.23/0.56  % (30378)------------------------------
% 0.23/0.56  % (30378)------------------------------
% 0.23/0.56  % (30383)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.56  % (30382)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.56  % (30393)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.57  % (30393)Refutation not found, incomplete strategy% (30393)------------------------------
% 0.23/0.57  % (30393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.57  % (30393)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.57  
% 0.23/0.57  % (30393)Memory used [KB]: 1663
% 0.23/0.57  % (30393)Time elapsed: 0.149 s
% 0.23/0.57  % (30393)------------------------------
% 0.23/0.57  % (30393)------------------------------
% 0.23/0.59  % (30381)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.23/0.59  % (30376)Refutation found. Thanks to Tanya!
% 0.23/0.59  % SZS status Theorem for theBenchmark
% 0.23/0.59  % SZS output start Proof for theBenchmark
% 0.23/0.59  fof(f285,plain,(
% 0.23/0.59    $false),
% 0.23/0.59    inference(avatar_sat_refutation,[],[f62,f63,f254,f284])).
% 0.23/0.59  fof(f284,plain,(
% 0.23/0.59    ~spl4_1 | ~spl4_2),
% 0.23/0.59    inference(avatar_contradiction_clause,[],[f283])).
% 0.23/0.59  fof(f283,plain,(
% 0.23/0.59    $false | (~spl4_1 | ~spl4_2)),
% 0.23/0.59    inference(subsumption_resolution,[],[f277,f52])).
% 0.23/0.59  fof(f52,plain,(
% 0.23/0.59    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.23/0.59    inference(equality_resolution,[],[f51])).
% 0.23/0.59  fof(f51,plain,(
% 0.23/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.23/0.59    inference(equality_resolution,[],[f42])).
% 0.23/0.59  fof(f42,plain,(
% 0.23/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.23/0.59    inference(cnf_transformation,[],[f32])).
% 0.23/0.59  fof(f32,plain,(
% 0.23/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.23/0.59  fof(f31,plain,(
% 0.23/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.23/0.59    introduced(choice_axiom,[])).
% 0.23/0.59  fof(f30,plain,(
% 0.23/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.59    inference(rectify,[],[f29])).
% 0.23/0.59  fof(f29,plain,(
% 0.23/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.23/0.59    inference(nnf_transformation,[],[f7])).
% 0.23/0.59  fof(f7,axiom,(
% 0.23/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.23/0.59  fof(f277,plain,(
% 0.23/0.59    ~r2_hidden(sK1,k1_tarski(sK1)) | (~spl4_1 | ~spl4_2)),
% 0.23/0.59    inference(resolution,[],[f272,f61])).
% 0.23/0.59  fof(f61,plain,(
% 0.23/0.59    r2_hidden(sK1,sK0) | ~spl4_2),
% 0.23/0.59    inference(avatar_component_clause,[],[f59])).
% 0.23/0.59  fof(f59,plain,(
% 0.23/0.59    spl4_2 <=> r2_hidden(sK1,sK0)),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.59  fof(f272,plain,(
% 0.23/0.59    ( ! [X4] : (~r2_hidden(X4,sK0) | ~r2_hidden(X4,k1_tarski(sK1))) ) | ~spl4_1),
% 0.23/0.59    inference(superposition,[],[f49,f56])).
% 0.23/0.59  fof(f56,plain,(
% 0.23/0.59    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl4_1),
% 0.23/0.59    inference(avatar_component_clause,[],[f55])).
% 0.23/0.59  fof(f55,plain,(
% 0.23/0.59    spl4_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.23/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.59  fof(f49,plain,(
% 0.23/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.23/0.59    inference(equality_resolution,[],[f36])).
% 0.23/0.59  fof(f36,plain,(
% 0.23/0.59    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.23/0.59    inference(cnf_transformation,[],[f28])).
% 0.23/0.59  fof(f28,plain,(
% 0.23/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.23/0.59  fof(f27,plain,(
% 0.23/0.59    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.23/0.59    introduced(choice_axiom,[])).
% 0.23/0.59  fof(f26,plain,(
% 0.23/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.59    inference(rectify,[],[f25])).
% 0.23/0.59  fof(f25,plain,(
% 0.23/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.59    inference(flattening,[],[f24])).
% 0.23/0.59  fof(f24,plain,(
% 0.23/0.59    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.23/0.59    inference(nnf_transformation,[],[f1])).
% 0.23/0.59  fof(f1,axiom,(
% 0.23/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.23/0.59  fof(f254,plain,(
% 0.23/0.59    spl4_1 | spl4_2),
% 0.23/0.59    inference(avatar_contradiction_clause,[],[f253])).
% 0.23/0.59  fof(f253,plain,(
% 0.23/0.59    $false | (spl4_1 | spl4_2)),
% 0.23/0.59    inference(subsumption_resolution,[],[f252,f52])).
% 0.23/0.59  fof(f252,plain,(
% 0.23/0.59    ~r2_hidden(sK1,k1_tarski(sK1)) | (spl4_1 | spl4_2)),
% 0.23/0.59    inference(subsumption_resolution,[],[f251,f57])).
% 0.23/0.59  fof(f57,plain,(
% 0.23/0.59    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | spl4_1),
% 0.23/0.59    inference(avatar_component_clause,[],[f55])).
% 0.23/0.59  fof(f251,plain,(
% 0.23/0.59    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | (spl4_1 | spl4_2)),
% 0.23/0.59    inference(subsumption_resolution,[],[f229,f60])).
% 0.23/0.59  fof(f60,plain,(
% 0.23/0.59    ~r2_hidden(sK1,sK0) | spl4_2),
% 0.23/0.59    inference(avatar_component_clause,[],[f59])).
% 0.23/0.59  fof(f229,plain,(
% 0.23/0.59    r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | spl4_1),
% 0.23/0.59    inference(superposition,[],[f39,f189])).
% 0.23/0.59  fof(f189,plain,(
% 0.23/0.59    sK1 = sK2(sK0,k1_tarski(sK1),sK0) | spl4_1),
% 0.23/0.59    inference(resolution,[],[f155,f53])).
% 0.23/0.59  fof(f53,plain,(
% 0.23/0.59    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 0.23/0.59    inference(equality_resolution,[],[f41])).
% 0.23/0.59  fof(f41,plain,(
% 0.23/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.23/0.59    inference(cnf_transformation,[],[f32])).
% 0.23/0.59  fof(f155,plain,(
% 0.23/0.59    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | spl4_1),
% 0.23/0.59    inference(subsumption_resolution,[],[f154,f147])).
% 0.23/0.59  fof(f147,plain,(
% 0.23/0.59    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 0.23/0.59    inference(duplicate_literal_removal,[],[f146])).
% 0.23/0.59  fof(f146,plain,(
% 0.23/0.59    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 0.23/0.59    inference(equality_resolution,[],[f68])).
% 0.23/0.59  fof(f68,plain,(
% 0.23/0.59    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0)) ) | spl4_1),
% 0.23/0.59    inference(superposition,[],[f57,f38])).
% 0.23/0.59  fof(f38,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f28])).
% 0.23/0.59  fof(f154,plain,(
% 0.23/0.59    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 0.23/0.59    inference(subsumption_resolution,[],[f148,f57])).
% 0.23/0.59  fof(f148,plain,(
% 0.23/0.59    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 0.23/0.59    inference(resolution,[],[f147,f40])).
% 0.23/0.59  fof(f40,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f28])).
% 0.23/0.59  fof(f39,plain,(
% 0.23/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 0.23/0.59    inference(cnf_transformation,[],[f28])).
% 0.23/0.59  fof(f63,plain,(
% 0.23/0.59    spl4_1 | ~spl4_2),
% 0.23/0.59    inference(avatar_split_clause,[],[f33,f59,f55])).
% 0.23/0.59  fof(f33,plain,(
% 0.23/0.59    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.23/0.59    inference(cnf_transformation,[],[f23])).
% 0.23/0.59  fof(f23,plain,(
% 0.23/0.59    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.23/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 0.23/0.59  fof(f22,plain,(
% 0.23/0.59    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 0.23/0.59    introduced(choice_axiom,[])).
% 0.23/0.59  fof(f21,plain,(
% 0.23/0.59    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 0.23/0.59    inference(nnf_transformation,[],[f20])).
% 0.23/0.59  fof(f20,plain,(
% 0.23/0.59    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.23/0.59    inference(ennf_transformation,[],[f18])).
% 0.23/0.59  fof(f18,negated_conjecture,(
% 0.23/0.59    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.23/0.59    inference(negated_conjecture,[],[f17])).
% 0.23/0.59  fof(f17,conjecture,(
% 0.23/0.59    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.23/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.23/0.59  fof(f62,plain,(
% 0.23/0.59    ~spl4_1 | spl4_2),
% 0.23/0.59    inference(avatar_split_clause,[],[f34,f59,f55])).
% 0.23/0.59  fof(f34,plain,(
% 0.23/0.59    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.23/0.59    inference(cnf_transformation,[],[f23])).
% 0.23/0.59  % SZS output end Proof for theBenchmark
% 0.23/0.59  % (30376)------------------------------
% 0.23/0.59  % (30376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.59  % (30376)Termination reason: Refutation
% 0.23/0.59  
% 0.23/0.59  % (30376)Memory used [KB]: 10746
% 0.23/0.59  % (30376)Time elapsed: 0.155 s
% 0.23/0.59  % (30376)------------------------------
% 0.23/0.59  % (30376)------------------------------
% 0.23/0.59  % (30363)Success in time 0.217 s
%------------------------------------------------------------------------------
