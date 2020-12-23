%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:57 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 107 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 367 expanded)
%              Number of equality atoms :   62 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f96,f171,f223,f252,f284,f299])).

fof(f299,plain,
    ( ~ spl5_8
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl5_8
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f283,f170,f283,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f170,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_8
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f283,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl5_13
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f284,plain,
    ( spl5_13
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f269,f92,f281])).

fof(f92,plain,
    ( spl5_4
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f269,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_4 ),
    inference(superposition,[],[f69,f94])).

fof(f94,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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

fof(f252,plain,
    ( spl5_1
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl5_1
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f248,f74])).

fof(f74,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f248,plain,
    ( sK0 = sK1
    | ~ spl5_9 ),
    inference(resolution,[],[f222,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f222,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl5_9
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f223,plain,
    ( spl5_9
    | spl5_3 ),
    inference(avatar_split_clause,[],[f214,f88,f220])).

fof(f88,plain,
    ( spl5_3
  <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f214,plain,
    ( r2_hidden(sK0,k1_tarski(sK1))
    | spl5_3 ),
    inference(resolution,[],[f200,f90])).

fof(f90,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f200,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(superposition,[],[f57,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( sK4(k1_tarski(X0),X1) = X0
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f56,f70])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f171,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f166,f168])).

fof(f166,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f96,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f85,f77,f92,f88])).

fof(f77,plain,
    ( spl5_2
  <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f85,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f79,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( sK0 != sK1
    & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f75,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 1.28/0.52  % (20426)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.53  % (20428)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.54  % (20434)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.39/0.54  % (20428)Refutation not found, incomplete strategy% (20428)------------------------------
% 1.39/0.54  % (20428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (20428)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (20428)Memory used [KB]: 1663
% 1.39/0.54  % (20428)Time elapsed: 0.039 s
% 1.39/0.54  % (20428)------------------------------
% 1.39/0.54  % (20428)------------------------------
% 1.39/0.54  % (20420)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (20414)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.55  % (20442)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.55  % (20419)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.39/0.56  % (20443)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.56  % (20429)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.56  % (20436)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.39/0.56  % (20435)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.57  % (20427)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.57  % (20424)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.57  % (20423)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.58  % (20421)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.39/0.58  % (20443)Refutation not found, incomplete strategy% (20443)------------------------------
% 1.39/0.58  % (20443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.58  % (20443)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.58  
% 1.39/0.58  % (20443)Memory used [KB]: 1663
% 1.39/0.58  % (20443)Time elapsed: 0.167 s
% 1.39/0.58  % (20443)------------------------------
% 1.39/0.58  % (20443)------------------------------
% 1.39/0.58  % (20415)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.59  % (20415)Refutation not found, incomplete strategy% (20415)------------------------------
% 1.39/0.59  % (20415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.59  % (20415)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.59  
% 1.39/0.59  % (20415)Memory used [KB]: 1663
% 1.39/0.59  % (20415)Time elapsed: 0.156 s
% 1.39/0.59  % (20415)------------------------------
% 1.39/0.59  % (20415)------------------------------
% 1.39/0.59  % (20437)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.59  % (20418)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.59  % (20435)Refutation found. Thanks to Tanya!
% 1.39/0.59  % SZS status Theorem for theBenchmark
% 1.39/0.59  % SZS output start Proof for theBenchmark
% 1.39/0.59  fof(f300,plain,(
% 1.39/0.59    $false),
% 1.39/0.59    inference(avatar_sat_refutation,[],[f75,f80,f96,f171,f223,f252,f284,f299])).
% 1.39/0.59  fof(f299,plain,(
% 1.39/0.59    ~spl5_8 | ~spl5_13),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f296])).
% 1.39/0.59  fof(f296,plain,(
% 1.39/0.59    $false | (~spl5_8 | ~spl5_13)),
% 1.39/0.59    inference(unit_resulting_resolution,[],[f283,f170,f283,f58])).
% 1.39/0.59  fof(f58,plain,(
% 1.39/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f33])).
% 1.39/0.59  fof(f33,plain,(
% 1.39/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.39/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f32])).
% 1.39/0.59  fof(f32,plain,(
% 1.39/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f18,plain,(
% 1.39/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.39/0.59    inference(ennf_transformation,[],[f15])).
% 1.39/0.59  fof(f15,plain,(
% 1.39/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.39/0.59    inference(rectify,[],[f3])).
% 1.39/0.59  fof(f3,axiom,(
% 1.39/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.39/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.39/0.59  fof(f170,plain,(
% 1.39/0.59    r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl5_8),
% 1.39/0.59    inference(avatar_component_clause,[],[f168])).
% 1.39/0.59  fof(f168,plain,(
% 1.39/0.59    spl5_8 <=> r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.39/0.59  fof(f283,plain,(
% 1.39/0.59    r2_hidden(sK0,k1_xboole_0) | ~spl5_13),
% 1.39/0.59    inference(avatar_component_clause,[],[f281])).
% 1.39/0.59  fof(f281,plain,(
% 1.39/0.59    spl5_13 <=> r2_hidden(sK0,k1_xboole_0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.39/0.59  fof(f284,plain,(
% 1.39/0.59    spl5_13 | ~spl5_4),
% 1.39/0.59    inference(avatar_split_clause,[],[f269,f92,f281])).
% 1.39/0.59  fof(f92,plain,(
% 1.39/0.59    spl5_4 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.39/0.59  fof(f269,plain,(
% 1.39/0.59    r2_hidden(sK0,k1_xboole_0) | ~spl5_4),
% 1.39/0.59    inference(superposition,[],[f69,f94])).
% 1.39/0.59  fof(f94,plain,(
% 1.39/0.59    k1_xboole_0 = k1_tarski(sK0) | ~spl5_4),
% 1.39/0.59    inference(avatar_component_clause,[],[f92])).
% 1.39/0.59  fof(f69,plain,(
% 1.39/0.59    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.39/0.59    inference(equality_resolution,[],[f68])).
% 1.39/0.59  fof(f68,plain,(
% 1.39/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.39/0.59    inference(equality_resolution,[],[f45])).
% 1.39/0.59  fof(f45,plain,(
% 1.39/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.39/0.59    inference(cnf_transformation,[],[f29])).
% 1.39/0.59  fof(f29,plain,(
% 1.39/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.39/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f28])).
% 1.39/0.59  fof(f28,plain,(
% 1.39/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f27,plain,(
% 1.39/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.39/0.59    inference(rectify,[],[f26])).
% 1.39/0.59  fof(f26,plain,(
% 1.39/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.39/0.59    inference(nnf_transformation,[],[f8])).
% 1.39/0.59  fof(f8,axiom,(
% 1.39/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.39/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.39/0.59  fof(f252,plain,(
% 1.39/0.59    spl5_1 | ~spl5_9),
% 1.39/0.59    inference(avatar_contradiction_clause,[],[f251])).
% 1.39/0.59  fof(f251,plain,(
% 1.39/0.59    $false | (spl5_1 | ~spl5_9)),
% 1.39/0.59    inference(subsumption_resolution,[],[f248,f74])).
% 1.39/0.59  fof(f74,plain,(
% 1.39/0.59    sK0 != sK1 | spl5_1),
% 1.39/0.59    inference(avatar_component_clause,[],[f72])).
% 1.39/0.59  fof(f72,plain,(
% 1.39/0.59    spl5_1 <=> sK0 = sK1),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.39/0.59  fof(f248,plain,(
% 1.39/0.59    sK0 = sK1 | ~spl5_9),
% 1.39/0.59    inference(resolution,[],[f222,f70])).
% 1.39/0.59  fof(f70,plain,(
% 1.39/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.39/0.59    inference(equality_resolution,[],[f44])).
% 1.39/0.59  fof(f44,plain,(
% 1.39/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.39/0.59    inference(cnf_transformation,[],[f29])).
% 1.39/0.59  fof(f222,plain,(
% 1.39/0.59    r2_hidden(sK0,k1_tarski(sK1)) | ~spl5_9),
% 1.39/0.59    inference(avatar_component_clause,[],[f220])).
% 1.39/0.59  fof(f220,plain,(
% 1.39/0.59    spl5_9 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.39/0.59  fof(f223,plain,(
% 1.39/0.59    spl5_9 | spl5_3),
% 1.39/0.59    inference(avatar_split_clause,[],[f214,f88,f220])).
% 1.39/0.59  fof(f88,plain,(
% 1.39/0.59    spl5_3 <=> r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.39/0.59  fof(f214,plain,(
% 1.39/0.59    r2_hidden(sK0,k1_tarski(sK1)) | spl5_3),
% 1.39/0.59    inference(resolution,[],[f200,f90])).
% 1.39/0.59  fof(f90,plain,(
% 1.39/0.59    ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_3),
% 1.39/0.59    inference(avatar_component_clause,[],[f88])).
% 1.39/0.59  fof(f200,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.39/0.59    inference(duplicate_literal_removal,[],[f197])).
% 1.39/0.59  fof(f197,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.39/0.59    inference(superposition,[],[f57,f101])).
% 1.39/0.59  fof(f101,plain,(
% 1.39/0.59    ( ! [X0,X1] : (sK4(k1_tarski(X0),X1) = X0 | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.39/0.59    inference(resolution,[],[f56,f70])).
% 1.39/0.59  fof(f56,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f33])).
% 1.39/0.59  fof(f57,plain,(
% 1.39/0.59    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f33])).
% 1.39/0.59  fof(f171,plain,(
% 1.39/0.59    spl5_8),
% 1.39/0.59    inference(avatar_split_clause,[],[f166,f168])).
% 1.39/0.59  fof(f166,plain,(
% 1.39/0.59    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.39/0.59    inference(equality_resolution,[],[f98])).
% 1.39/0.59  fof(f98,plain,(
% 1.39/0.59    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 1.39/0.59    inference(superposition,[],[f54,f52])).
% 1.39/0.59  fof(f52,plain,(
% 1.39/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.39/0.59    inference(cnf_transformation,[],[f14])).
% 1.39/0.59  fof(f14,plain,(
% 1.39/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.39/0.59    inference(rectify,[],[f2])).
% 1.39/0.59  fof(f2,axiom,(
% 1.39/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.39/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.39/0.59  fof(f54,plain,(
% 1.39/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f31])).
% 1.39/0.59  fof(f31,plain,(
% 1.39/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.39/0.59    inference(nnf_transformation,[],[f1])).
% 1.39/0.59  fof(f1,axiom,(
% 1.39/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.39/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.39/0.59  fof(f96,plain,(
% 1.39/0.59    ~spl5_3 | spl5_4 | ~spl5_2),
% 1.39/0.59    inference(avatar_split_clause,[],[f85,f77,f92,f88])).
% 1.39/0.59  fof(f77,plain,(
% 1.39/0.59    spl5_2 <=> k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.39/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.39/0.59  fof(f85,plain,(
% 1.39/0.59    k1_xboole_0 = k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl5_2),
% 1.39/0.59    inference(superposition,[],[f79,f53])).
% 1.39/0.59  fof(f53,plain,(
% 1.39/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.39/0.59    inference(cnf_transformation,[],[f31])).
% 1.39/0.59  fof(f79,plain,(
% 1.39/0.59    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~spl5_2),
% 1.39/0.59    inference(avatar_component_clause,[],[f77])).
% 1.39/0.59  fof(f80,plain,(
% 1.39/0.59    spl5_2),
% 1.39/0.59    inference(avatar_split_clause,[],[f34,f77])).
% 1.39/0.59  fof(f34,plain,(
% 1.39/0.59    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.39/0.59    inference(cnf_transformation,[],[f20])).
% 1.39/0.59  fof(f20,plain,(
% 1.39/0.59    sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.39/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f19])).
% 1.39/0.59  fof(f19,plain,(
% 1.39/0.59    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.39/0.59    introduced(choice_axiom,[])).
% 1.39/0.59  fof(f16,plain,(
% 1.39/0.59    ? [X0,X1] : (X0 != X1 & k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.39/0.59    inference(ennf_transformation,[],[f13])).
% 1.39/0.59  fof(f13,negated_conjecture,(
% 1.39/0.59    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.39/0.59    inference(negated_conjecture,[],[f12])).
% 1.39/0.59  fof(f12,conjecture,(
% 1.39/0.59    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.39/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 1.39/0.59  fof(f75,plain,(
% 1.39/0.59    ~spl5_1),
% 1.39/0.59    inference(avatar_split_clause,[],[f35,f72])).
% 1.39/0.59  fof(f35,plain,(
% 1.39/0.59    sK0 != sK1),
% 1.39/0.59    inference(cnf_transformation,[],[f20])).
% 1.39/0.59  % SZS output end Proof for theBenchmark
% 1.39/0.59  % (20435)------------------------------
% 1.39/0.59  % (20435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.59  % (20435)Termination reason: Refutation
% 1.39/0.59  
% 1.39/0.59  % (20435)Memory used [KB]: 6396
% 1.39/0.59  % (20435)Time elapsed: 0.162 s
% 1.39/0.59  % (20435)------------------------------
% 1.39/0.59  % (20435)------------------------------
% 1.39/0.59  % (20413)Success in time 0.231 s
%------------------------------------------------------------------------------
