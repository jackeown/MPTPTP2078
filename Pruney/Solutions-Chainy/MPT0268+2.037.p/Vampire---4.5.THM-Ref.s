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
% DateTime   : Thu Dec  3 12:40:41 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
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
fof(f280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f58,f249,f279])).

fof(f279,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f272,f47])).

fof(f47,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
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

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f27,plain,(
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

fof(f272,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f267,f56])).

fof(f56,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f267,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK0)
        | ~ r2_hidden(X4,k1_tarski(sK1)) )
    | ~ spl4_1 ),
    inference(superposition,[],[f44,f51])).

fof(f51,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f25,plain,(
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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f249,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f247,f47])).

fof(f247,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f246,f52])).

fof(f52,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f246,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f224,f55])).

fof(f55,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f224,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | spl4_1 ),
    inference(superposition,[],[f37,f184])).

fof(f184,plain,
    ( sK1 = sK2(sK0,k1_tarski(sK1),sK0)
    | spl4_1 ),
    inference(resolution,[],[f150,f48])).

fof(f48,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f150,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f149,f142])).

fof(f142,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,
    ( ! [X0] :
        ( sK0 != X0
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0)
        | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0) )
    | spl4_1 ),
    inference(superposition,[],[f52,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X0)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f149,plain,
    ( r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f143,f52])).

fof(f143,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1))
    | ~ r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0)
    | spl4_1 ),
    inference(resolution,[],[f142,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f31,f54,f50])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).

fof(f20,plain,
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

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f57,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f32,f54,f50])).

fof(f32,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (5850)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (5845)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (5838)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (5839)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.52  % (5847)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.52  % (5859)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.22/0.52  % (5853)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.52  % (5857)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.52  % (5855)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.22/0.53  % (5835)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.22/0.53  % (5849)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.22/0.53  % (5836)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.53  % (5836)Refutation not found, incomplete strategy% (5836)------------------------------
% 1.22/0.53  % (5836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (5836)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (5836)Memory used [KB]: 1663
% 1.22/0.53  % (5836)Time elapsed: 0.124 s
% 1.22/0.53  % (5836)------------------------------
% 1.22/0.53  % (5836)------------------------------
% 1.22/0.53  % (5837)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (5840)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.53  % (5863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.53  % (5844)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.53  % (5861)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.53  % (5854)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.53  % (5861)Refutation not found, incomplete strategy% (5861)------------------------------
% 1.41/0.53  % (5861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5861)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (5861)Memory used [KB]: 6140
% 1.41/0.54  % (5861)Time elapsed: 0.140 s
% 1.41/0.54  % (5861)------------------------------
% 1.41/0.54  % (5861)------------------------------
% 1.41/0.54  % (5860)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.41/0.54  % (5846)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.54  % (5862)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.54  % (5858)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.54  % (5864)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.54  % (5864)Refutation not found, incomplete strategy% (5864)------------------------------
% 1.41/0.54  % (5864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5864)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (5864)Memory used [KB]: 1663
% 1.41/0.54  % (5864)Time elapsed: 0.139 s
% 1.41/0.54  % (5864)------------------------------
% 1.41/0.54  % (5864)------------------------------
% 1.41/0.54  % (5846)Refutation not found, incomplete strategy% (5846)------------------------------
% 1.41/0.54  % (5846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5846)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (5846)Memory used [KB]: 6140
% 1.41/0.54  % (5846)Time elapsed: 0.139 s
% 1.41/0.54  % (5846)------------------------------
% 1.41/0.54  % (5846)------------------------------
% 1.41/0.54  % (5856)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.54  % (5849)Refutation not found, incomplete strategy% (5849)------------------------------
% 1.41/0.54  % (5849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5849)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (5849)Memory used [KB]: 1663
% 1.41/0.54  % (5849)Time elapsed: 0.111 s
% 1.41/0.54  % (5849)------------------------------
% 1.41/0.54  % (5849)------------------------------
% 1.41/0.54  % (5851)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.54  % (5852)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.54  % (5852)Refutation not found, incomplete strategy% (5852)------------------------------
% 1.41/0.54  % (5852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5852)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (5852)Memory used [KB]: 1663
% 1.41/0.54  % (5852)Time elapsed: 0.149 s
% 1.41/0.54  % (5852)------------------------------
% 1.41/0.54  % (5852)------------------------------
% 1.41/0.54  % (5851)Refutation not found, incomplete strategy% (5851)------------------------------
% 1.41/0.54  % (5851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (5851)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (5851)Memory used [KB]: 10618
% 1.41/0.54  % (5851)Time elapsed: 0.145 s
% 1.41/0.54  % (5851)------------------------------
% 1.41/0.54  % (5851)------------------------------
% 1.41/0.54  % (5841)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.41/0.55  % (5843)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.55  % (5848)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.55  % (5847)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f280,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f57,f58,f249,f279])).
% 1.41/0.55  fof(f279,plain,(
% 1.41/0.55    ~spl4_1 | ~spl4_2),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f278])).
% 1.41/0.55  fof(f278,plain,(
% 1.41/0.55    $false | (~spl4_1 | ~spl4_2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f272,f47])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.41/0.55    inference(equality_resolution,[],[f46])).
% 1.41/0.55  fof(f46,plain,(
% 1.41/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.41/0.55    inference(equality_resolution,[],[f40])).
% 1.41/0.55  fof(f40,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.41/0.55    inference(rectify,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.41/0.55    inference(nnf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.41/0.55  fof(f272,plain,(
% 1.41/0.55    ~r2_hidden(sK1,k1_tarski(sK1)) | (~spl4_1 | ~spl4_2)),
% 1.41/0.55    inference(resolution,[],[f267,f56])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    r2_hidden(sK1,sK0) | ~spl4_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f54])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    spl4_2 <=> r2_hidden(sK1,sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.41/0.55  fof(f267,plain,(
% 1.41/0.55    ( ! [X4] : (~r2_hidden(X4,sK0) | ~r2_hidden(X4,k1_tarski(sK1))) ) | ~spl4_1),
% 1.41/0.55    inference(superposition,[],[f44,f51])).
% 1.41/0.55  fof(f51,plain,(
% 1.41/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl4_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f50])).
% 1.41/0.55  fof(f50,plain,(
% 1.41/0.55    spl4_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.41/0.55  fof(f44,plain,(
% 1.41/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.41/0.55    inference(equality_resolution,[],[f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f26,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.41/0.55  fof(f25,plain,(
% 1.41/0.55    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(rectify,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(flattening,[],[f22])).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.55    inference(nnf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.55  fof(f249,plain,(
% 1.41/0.55    spl4_1 | spl4_2),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f248])).
% 1.41/0.55  fof(f248,plain,(
% 1.41/0.55    $false | (spl4_1 | spl4_2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f247,f47])).
% 1.41/0.55  fof(f247,plain,(
% 1.41/0.55    ~r2_hidden(sK1,k1_tarski(sK1)) | (spl4_1 | spl4_2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f246,f52])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | spl4_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f50])).
% 1.41/0.55  fof(f246,plain,(
% 1.41/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | (spl4_1 | spl4_2)),
% 1.41/0.55    inference(subsumption_resolution,[],[f224,f55])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ~r2_hidden(sK1,sK0) | spl4_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f54])).
% 1.41/0.55  fof(f224,plain,(
% 1.41/0.55    r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | spl4_1),
% 1.41/0.55    inference(superposition,[],[f37,f184])).
% 1.41/0.55  fof(f184,plain,(
% 1.41/0.55    sK1 = sK2(sK0,k1_tarski(sK1),sK0) | spl4_1),
% 1.41/0.55    inference(resolution,[],[f150,f48])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.41/0.55    inference(equality_resolution,[],[f39])).
% 1.41/0.55  fof(f39,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f150,plain,(
% 1.41/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | spl4_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f149,f142])).
% 1.41/0.55  fof(f142,plain,(
% 1.41/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f141])).
% 1.41/0.55  fof(f141,plain,(
% 1.41/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 1.41/0.55    inference(equality_resolution,[],[f63])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ( ! [X0] : (sK0 != X0 | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),sK0) | r2_hidden(sK2(sK0,k1_tarski(sK1),X0),X0)) ) | spl4_1),
% 1.41/0.55    inference(superposition,[],[f52,f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f149,plain,(
% 1.41/0.55    r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f143,f52])).
% 1.41/0.55  fof(f143,plain,(
% 1.41/0.55    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),k1_tarski(sK1)) | ~r2_hidden(sK2(sK0,k1_tarski(sK1),sK0),sK0) | spl4_1),
% 1.41/0.55    inference(resolution,[],[f142,f38])).
% 1.41/0.55  fof(f38,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f26])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    spl4_1 | ~spl4_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f31,f54,f50])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.41/0.55    inference(cnf_transformation,[],[f21])).
% 1.41/0.55  fof(f21,plain,(
% 1.41/0.55    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f20])).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.41/0.55    inference(nnf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f17])).
% 1.41/0.55  fof(f17,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.41/0.55    inference(negated_conjecture,[],[f16])).
% 1.41/0.55  fof(f16,conjecture,(
% 1.41/0.55    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.41/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    ~spl4_1 | spl4_2),
% 1.41/0.55    inference(avatar_split_clause,[],[f32,f54,f50])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.41/0.55    inference(cnf_transformation,[],[f21])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (5847)------------------------------
% 1.41/0.55  % (5847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (5847)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (5847)Memory used [KB]: 10746
% 1.41/0.55  % (5847)Time elapsed: 0.153 s
% 1.41/0.55  % (5847)------------------------------
% 1.41/0.55  % (5847)------------------------------
% 1.41/0.55  % (5834)Success in time 0.19 s
%------------------------------------------------------------------------------
