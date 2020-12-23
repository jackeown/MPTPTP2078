%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:11 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 100 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  179 ( 368 expanded)
%              Number of equality atoms :   30 (  58 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f256,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f235,f241,f255])).

fof(f255,plain,
    ( spl5_2
    | spl5_5 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl5_2
    | spl5_5 ),
    inference(subsumption_resolution,[],[f252,f51])).

fof(f51,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f252,plain,
    ( r2_hidden(sK2,sK1)
    | spl5_5 ),
    inference(resolution,[],[f234,f89])).

fof(f89,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,k1_tarski(X3))
      | r2_hidden(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X3] :
      ( r2_hidden(X3,X2)
      | r1_xboole_0(X2,k1_tarski(X3))
      | r1_xboole_0(X2,k1_tarski(X3)) ) ),
    inference(superposition,[],[f30,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sK3(X0,k1_tarski(X1)) = X1
      | r1_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(resolution,[],[f31,f42])).

fof(f42,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f234,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl5_5
  <=> r1_xboole_0(sK1,k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f241,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f238,f56])).

fof(f56,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f238,plain,
    ( r2_hidden(sK0,sK1)
    | spl5_4 ),
    inference(resolution,[],[f230,f89])).

fof(f230,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl5_4
  <=> r1_xboole_0(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f235,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f216,f44,f232,f228])).

fof(f44,plain,
    ( spl5_1
  <=> r1_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f216,plain,
    ( ~ r1_xboole_0(sK1,k1_tarski(sK2))
    | ~ r1_xboole_0(sK1,k1_tarski(sK0))
    | spl5_1 ),
    inference(resolution,[],[f122,f46])).

fof(f46,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r1_xboole_0(X2,k1_tarski(X1))
      | ~ r1_xboole_0(X2,k1_tarski(X0)) ) ),
    inference(superposition,[],[f68,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f68,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(k2_xboole_0(X7,X8),X6)
      | ~ r1_xboole_0(X6,X8)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(resolution,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f57,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ~ r2_hidden(sK2,sK1)
    & ~ r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) )
   => ( ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ~ r2_hidden(sK2,sK1)
      & ~ r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
      & ~ r2_hidden(X2,X1)
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
          & ~ r2_hidden(X2,X1)
          & ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f52,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f25,f44])).

fof(f25,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (4559)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (4561)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (4558)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (4569)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (4569)Refutation not found, incomplete strategy% (4569)------------------------------
% 0.21/0.52  % (4569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4569)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4569)Memory used [KB]: 1663
% 0.21/0.52  % (4569)Time elapsed: 0.106 s
% 0.21/0.52  % (4569)------------------------------
% 0.21/0.52  % (4569)------------------------------
% 0.21/0.52  % (4560)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (4567)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (4573)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (4557)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (4570)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (4577)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (4562)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (4556)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (4565)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (4578)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (4574)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (4556)Refutation not found, incomplete strategy% (4556)------------------------------
% 0.21/0.54  % (4556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (4581)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (4556)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4556)Memory used [KB]: 1663
% 0.21/0.54  % (4556)Time elapsed: 0.119 s
% 0.21/0.54  % (4556)------------------------------
% 0.21/0.54  % (4556)------------------------------
% 0.21/0.54  % (4583)Refutation not found, incomplete strategy% (4583)------------------------------
% 0.21/0.54  % (4583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4583)Memory used [KB]: 10618
% 0.21/0.54  % (4583)Time elapsed: 0.130 s
% 0.21/0.54  % (4583)------------------------------
% 0.21/0.54  % (4583)------------------------------
% 0.21/0.54  % (4572)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (4581)Refutation not found, incomplete strategy% (4581)------------------------------
% 0.21/0.54  % (4581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4581)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4581)Memory used [KB]: 6140
% 0.21/0.54  % (4581)Time elapsed: 0.137 s
% 0.21/0.54  % (4581)------------------------------
% 0.21/0.54  % (4581)------------------------------
% 0.21/0.54  % (4572)Refutation not found, incomplete strategy% (4572)------------------------------
% 0.21/0.54  % (4572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4572)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4572)Memory used [KB]: 1663
% 0.21/0.54  % (4572)Time elapsed: 0.136 s
% 0.21/0.54  % (4572)------------------------------
% 0.21/0.54  % (4572)------------------------------
% 0.21/0.54  % (4555)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (4580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (4579)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (4575)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (4576)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (4584)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (4584)Refutation not found, incomplete strategy% (4584)------------------------------
% 0.21/0.55  % (4584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (4584)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (4584)Memory used [KB]: 1663
% 0.21/0.55  % (4584)Time elapsed: 0.140 s
% 0.21/0.55  % (4584)------------------------------
% 0.21/0.55  % (4584)------------------------------
% 0.21/0.55  % (4563)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.55  % (4566)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.55  % (4576)Refutation found. Thanks to Tanya!
% 1.46/0.55  % SZS status Theorem for theBenchmark
% 1.46/0.55  % SZS output start Proof for theBenchmark
% 1.46/0.55  fof(f256,plain,(
% 1.46/0.55    $false),
% 1.46/0.55    inference(avatar_sat_refutation,[],[f47,f52,f57,f235,f241,f255])).
% 1.46/0.55  fof(f255,plain,(
% 1.46/0.55    spl5_2 | spl5_5),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f254])).
% 1.46/0.55  fof(f254,plain,(
% 1.46/0.55    $false | (spl5_2 | spl5_5)),
% 1.46/0.55    inference(subsumption_resolution,[],[f252,f51])).
% 1.46/0.55  fof(f51,plain,(
% 1.46/0.55    ~r2_hidden(sK2,sK1) | spl5_2),
% 1.46/0.55    inference(avatar_component_clause,[],[f49])).
% 1.46/0.55  fof(f49,plain,(
% 1.46/0.55    spl5_2 <=> r2_hidden(sK2,sK1)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.46/0.55  fof(f252,plain,(
% 1.46/0.55    r2_hidden(sK2,sK1) | spl5_5),
% 1.46/0.55    inference(resolution,[],[f234,f89])).
% 1.46/0.55  fof(f89,plain,(
% 1.46/0.55    ( ! [X2,X3] : (r1_xboole_0(X2,k1_tarski(X3)) | r2_hidden(X3,X2)) )),
% 1.46/0.55    inference(duplicate_literal_removal,[],[f86])).
% 1.46/0.55  fof(f86,plain,(
% 1.46/0.55    ( ! [X2,X3] : (r2_hidden(X3,X2) | r1_xboole_0(X2,k1_tarski(X3)) | r1_xboole_0(X2,k1_tarski(X3))) )),
% 1.46/0.55    inference(superposition,[],[f30,f60])).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    ( ! [X0,X1] : (sK3(X0,k1_tarski(X1)) = X1 | r1_xboole_0(X0,k1_tarski(X1))) )),
% 1.46/0.55    inference(resolution,[],[f31,f42])).
% 1.46/0.55  fof(f42,plain,(
% 1.46/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.46/0.55    inference(equality_resolution,[],[f36])).
% 1.46/0.55  fof(f36,plain,(
% 1.46/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f20,plain,(
% 1.46/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.46/0.55    inference(rectify,[],[f19])).
% 1.46/0.55  fof(f19,plain,(
% 1.46/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.46/0.55    inference(nnf_transformation,[],[f4])).
% 1.46/0.55  fof(f4,axiom,(
% 1.46/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.46/0.55  fof(f31,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f18])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f17])).
% 1.46/0.55  fof(f17,plain,(
% 1.46/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f14,plain,(
% 1.46/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.46/0.55    inference(ennf_transformation,[],[f10])).
% 1.46/0.55  fof(f10,plain,(
% 1.46/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.46/0.55    inference(rectify,[],[f2])).
% 1.46/0.55  fof(f2,axiom,(
% 1.46/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.46/0.55  fof(f30,plain,(
% 1.46/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f18])).
% 1.46/0.55  fof(f234,plain,(
% 1.46/0.55    ~r1_xboole_0(sK1,k1_tarski(sK2)) | spl5_5),
% 1.46/0.55    inference(avatar_component_clause,[],[f232])).
% 1.46/0.55  fof(f232,plain,(
% 1.46/0.55    spl5_5 <=> r1_xboole_0(sK1,k1_tarski(sK2))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.46/0.55  fof(f241,plain,(
% 1.46/0.55    spl5_3 | spl5_4),
% 1.46/0.55    inference(avatar_contradiction_clause,[],[f240])).
% 1.46/0.55  fof(f240,plain,(
% 1.46/0.55    $false | (spl5_3 | spl5_4)),
% 1.46/0.55    inference(subsumption_resolution,[],[f238,f56])).
% 1.46/0.55  fof(f56,plain,(
% 1.46/0.55    ~r2_hidden(sK0,sK1) | spl5_3),
% 1.46/0.55    inference(avatar_component_clause,[],[f54])).
% 1.46/0.55  fof(f54,plain,(
% 1.46/0.55    spl5_3 <=> r2_hidden(sK0,sK1)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.46/0.55  fof(f238,plain,(
% 1.46/0.55    r2_hidden(sK0,sK1) | spl5_4),
% 1.46/0.55    inference(resolution,[],[f230,f89])).
% 1.46/0.55  fof(f230,plain,(
% 1.46/0.55    ~r1_xboole_0(sK1,k1_tarski(sK0)) | spl5_4),
% 1.46/0.55    inference(avatar_component_clause,[],[f228])).
% 1.46/0.55  fof(f228,plain,(
% 1.46/0.55    spl5_4 <=> r1_xboole_0(sK1,k1_tarski(sK0))),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.46/0.55  fof(f235,plain,(
% 1.46/0.55    ~spl5_4 | ~spl5_5 | spl5_1),
% 1.46/0.55    inference(avatar_split_clause,[],[f216,f44,f232,f228])).
% 1.46/0.55  fof(f44,plain,(
% 1.46/0.55    spl5_1 <=> r1_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.46/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.46/0.55  fof(f216,plain,(
% 1.46/0.55    ~r1_xboole_0(sK1,k1_tarski(sK2)) | ~r1_xboole_0(sK1,k1_tarski(sK0)) | spl5_1),
% 1.46/0.55    inference(resolution,[],[f122,f46])).
% 1.46/0.55  fof(f46,plain,(
% 1.46/0.55    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1) | spl5_1),
% 1.46/0.55    inference(avatar_component_clause,[],[f44])).
% 1.46/0.55  fof(f122,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X1),X2) | ~r1_xboole_0(X2,k1_tarski(X1)) | ~r1_xboole_0(X2,k1_tarski(X0))) )),
% 1.46/0.55    inference(superposition,[],[f68,f34])).
% 1.46/0.55  fof(f34,plain,(
% 1.46/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f5])).
% 1.46/0.55  fof(f5,axiom,(
% 1.46/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.46/0.55  fof(f68,plain,(
% 1.46/0.55    ( ! [X6,X8,X7] : (r1_xboole_0(k2_xboole_0(X7,X8),X6) | ~r1_xboole_0(X6,X8) | ~r1_xboole_0(X6,X7)) )),
% 1.46/0.55    inference(resolution,[],[f26,f29])).
% 1.46/0.55  fof(f29,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f13])).
% 1.46/0.55  fof(f13,plain,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.46/0.55  fof(f26,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.46/0.55    inference(cnf_transformation,[],[f12])).
% 1.46/0.55  fof(f12,plain,(
% 1.46/0.55    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.46/0.55    inference(ennf_transformation,[],[f3])).
% 1.46/0.55  fof(f3,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.46/0.55  fof(f57,plain,(
% 1.46/0.55    ~spl5_3),
% 1.46/0.55    inference(avatar_split_clause,[],[f23,f54])).
% 1.46/0.55  fof(f23,plain,(
% 1.46/0.55    ~r2_hidden(sK0,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f16])).
% 1.46/0.55  fof(f16,plain,(
% 1.46/0.55    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1) & ~r2_hidden(sK2,sK1) & ~r2_hidden(sK0,sK1)),
% 1.46/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 1.46/0.55  fof(f15,plain,(
% 1.46/0.55    ? [X0,X1,X2] : (~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1)) => (~r1_xboole_0(k2_tarski(sK0,sK2),sK1) & ~r2_hidden(sK2,sK1) & ~r2_hidden(sK0,sK1))),
% 1.46/0.55    introduced(choice_axiom,[])).
% 1.46/0.55  fof(f11,plain,(
% 1.46/0.55    ? [X0,X1,X2] : (~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.46/0.55    inference(ennf_transformation,[],[f9])).
% 1.46/0.55  fof(f9,negated_conjecture,(
% 1.46/0.55    ~! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.46/0.55    inference(negated_conjecture,[],[f8])).
% 1.46/0.55  fof(f8,conjecture,(
% 1.46/0.55    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 1.46/0.55  fof(f52,plain,(
% 1.46/0.55    ~spl5_2),
% 1.46/0.55    inference(avatar_split_clause,[],[f24,f49])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    ~r2_hidden(sK2,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f16])).
% 1.46/0.55  fof(f47,plain,(
% 1.46/0.55    ~spl5_1),
% 1.46/0.55    inference(avatar_split_clause,[],[f25,f44])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    ~r1_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f16])).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (4576)------------------------------
% 1.46/0.55  % (4576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (4576)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (4576)Memory used [KB]: 6268
% 1.46/0.55  % (4576)Time elapsed: 0.144 s
% 1.46/0.55  % (4576)------------------------------
% 1.46/0.55  % (4576)------------------------------
% 1.46/0.55  % (4554)Success in time 0.184 s
%------------------------------------------------------------------------------
