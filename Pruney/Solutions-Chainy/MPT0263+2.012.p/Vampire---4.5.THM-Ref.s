%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:13 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   50 (  91 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  212 ( 439 expanded)
%              Number of equality atoms :   54 ( 133 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f674,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f671,f673])).

fof(f673,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f160,f143])).

fof(f143,plain,
    ( spl5_3
  <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f160,plain,(
    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( k1_tarski(sK0) != X0
      | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),k1_tarski(sK0))
      | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),X0) ) ),
    inference(superposition,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f28,plain,(
    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
    & ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)
      & ~ r1_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

fof(f671,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f670])).

fof(f670,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f669,f86])).

fof(f86,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f50,f69])).

fof(f69,plain,(
    sK0 = sK2(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f49,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
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

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f49,plain,(
    r2_hidden(sK2(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(resolution,[],[f27,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f27,plain,(
    ~ r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    r2_hidden(sK2(k1_tarski(sK0),sK1),sK1) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f669,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f668,f28])).

fof(f668,plain,
    ( k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f652,f44])).

fof(f44,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f652,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f651])).

fof(f651,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK0))
    | k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)
    | ~ r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(superposition,[],[f42,f290])).

fof(f290,plain,
    ( sK0 = sK4(k1_tarski(sK0),sK1,k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(resolution,[],[f145,f45])).

fof(f145,plain,
    ( r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f143])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (25193)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (25186)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (25197)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (25205)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (25189)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.54  % (25213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.54  % (25190)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (25191)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (25194)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.55  % (25195)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (25209)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.39/0.55  % (25199)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.39/0.55  % (25187)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.55  % (25199)Refutation not found, incomplete strategy% (25199)------------------------------
% 1.39/0.55  % (25199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25199)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25199)Memory used [KB]: 1663
% 1.39/0.55  % (25199)Time elapsed: 0.065 s
% 1.39/0.55  % (25199)------------------------------
% 1.39/0.55  % (25199)------------------------------
% 1.39/0.55  % (25211)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (25185)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.39/0.56  % (25211)Refutation not found, incomplete strategy% (25211)------------------------------
% 1.39/0.56  % (25211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (25211)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (25211)Memory used [KB]: 6140
% 1.39/0.56  % (25211)Time elapsed: 0.150 s
% 1.39/0.56  % (25211)------------------------------
% 1.39/0.56  % (25211)------------------------------
% 1.39/0.56  % (25206)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.39/0.56  % (25208)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.56  % (25196)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.39/0.57  % (25198)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.39/0.57  % (25212)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.64/0.57  % (25212)Refutation not found, incomplete strategy% (25212)------------------------------
% 1.64/0.57  % (25212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (25212)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (25212)Memory used [KB]: 6140
% 1.64/0.57  % (25212)Time elapsed: 0.158 s
% 1.64/0.57  % (25212)------------------------------
% 1.64/0.57  % (25212)------------------------------
% 1.64/0.57  % (25188)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.64/0.57  % (25209)Refutation not found, incomplete strategy% (25209)------------------------------
% 1.64/0.57  % (25209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (25209)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.57  
% 1.64/0.57  % (25209)Memory used [KB]: 10618
% 1.64/0.57  % (25209)Time elapsed: 0.158 s
% 1.64/0.57  % (25209)------------------------------
% 1.64/0.57  % (25209)------------------------------
% 1.64/0.57  % (25204)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.64/0.57  % (25207)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.64/0.57  % (25192)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.64/0.58  % (25214)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.64/0.58  % (25210)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.64/0.58  % (25203)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.64/0.58  % (25203)Refutation not found, incomplete strategy% (25203)------------------------------
% 1.64/0.58  % (25203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (25203)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (25203)Memory used [KB]: 1663
% 1.64/0.58  % (25203)Time elapsed: 0.169 s
% 1.64/0.58  % (25203)------------------------------
% 1.64/0.58  % (25203)------------------------------
% 1.64/0.58  % (25200)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.64/0.59  % (25197)Refutation found. Thanks to Tanya!
% 1.64/0.59  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  fof(f674,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(avatar_sat_refutation,[],[f671,f673])).
% 1.64/0.59  fof(f673,plain,(
% 1.64/0.59    spl5_3),
% 1.64/0.59    inference(avatar_split_clause,[],[f160,f143])).
% 1.64/0.59  fof(f143,plain,(
% 1.64/0.59    spl5_3 <=> r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.64/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.64/0.59  fof(f160,plain,(
% 1.64/0.59    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f159])).
% 1.64/0.59  fof(f159,plain,(
% 1.64/0.59    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 1.64/0.59    inference(equality_resolution,[],[f56])).
% 1.64/0.59  fof(f56,plain,(
% 1.64/0.59    ( ! [X0] : (k1_tarski(sK0) != X0 | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),k1_tarski(sK0)) | r2_hidden(sK4(k1_tarski(sK0),sK1,X0),X0)) )),
% 1.64/0.59    inference(superposition,[],[f28,f40])).
% 1.64/0.59  fof(f40,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f26])).
% 1.64/0.59  fof(f26,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).
% 1.64/0.59  fof(f25,plain,(
% 1.64/0.59    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f24,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(rectify,[],[f23])).
% 1.64/0.59  fof(f23,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(flattening,[],[f22])).
% 1.64/0.59  fof(f22,plain,(
% 1.64/0.59    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.64/0.59    inference(nnf_transformation,[],[f2])).
% 1.64/0.59  fof(f2,axiom,(
% 1.64/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.64/0.59  fof(f28,plain,(
% 1.64/0.59    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f15])).
% 1.64/0.59  fof(f15,plain,(
% 1.64/0.59    k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14])).
% 1.64/0.59  fof(f14,plain,(
% 1.64/0.59    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k3_xboole_0(k1_tarski(sK0),sK1) & ~r1_xboole_0(k1_tarski(sK0),sK1))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f12,plain,(
% 1.64/0.59    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),X1) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.64/0.59    inference(ennf_transformation,[],[f10])).
% 1.64/0.59  fof(f10,negated_conjecture,(
% 1.64/0.59    ~! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.64/0.59    inference(negated_conjecture,[],[f9])).
% 1.64/0.59  fof(f9,conjecture,(
% 1.64/0.59    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) | r1_xboole_0(k1_tarski(X0),X1))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).
% 1.64/0.59  fof(f671,plain,(
% 1.64/0.59    ~spl5_3),
% 1.64/0.59    inference(avatar_contradiction_clause,[],[f670])).
% 1.64/0.59  fof(f670,plain,(
% 1.64/0.59    $false | ~spl5_3),
% 1.64/0.59    inference(subsumption_resolution,[],[f669,f86])).
% 1.64/0.59  fof(f86,plain,(
% 1.64/0.59    r2_hidden(sK0,sK1)),
% 1.64/0.59    inference(superposition,[],[f50,f69])).
% 1.64/0.59  fof(f69,plain,(
% 1.64/0.59    sK0 = sK2(k1_tarski(sK0),sK1)),
% 1.64/0.59    inference(resolution,[],[f49,f45])).
% 1.64/0.59  fof(f45,plain,(
% 1.64/0.59    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 1.64/0.59    inference(equality_resolution,[],[f33])).
% 1.64/0.59  fof(f33,plain,(
% 1.64/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.64/0.59    inference(cnf_transformation,[],[f21])).
% 1.64/0.59  fof(f21,plain,(
% 1.64/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 1.64/0.59  fof(f20,plain,(
% 1.64/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f19,plain,(
% 1.64/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.59    inference(rectify,[],[f18])).
% 1.64/0.59  fof(f18,plain,(
% 1.64/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.64/0.59    inference(nnf_transformation,[],[f5])).
% 1.64/0.59  fof(f5,axiom,(
% 1.64/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.64/0.59  fof(f49,plain,(
% 1.64/0.59    r2_hidden(sK2(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 1.64/0.59    inference(resolution,[],[f27,f30])).
% 1.64/0.59  fof(f30,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f17])).
% 1.64/0.59  fof(f17,plain,(
% 1.64/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.64/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f16])).
% 1.64/0.59  fof(f16,plain,(
% 1.64/0.59    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.64/0.59    introduced(choice_axiom,[])).
% 1.64/0.59  fof(f13,plain,(
% 1.64/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.64/0.59    inference(ennf_transformation,[],[f11])).
% 1.64/0.59  fof(f11,plain,(
% 1.64/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.59    inference(rectify,[],[f3])).
% 1.64/0.59  fof(f3,axiom,(
% 1.64/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.64/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.64/0.59  fof(f27,plain,(
% 1.64/0.59    ~r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.64/0.59    inference(cnf_transformation,[],[f15])).
% 1.64/0.59  fof(f50,plain,(
% 1.64/0.59    r2_hidden(sK2(k1_tarski(sK0),sK1),sK1)),
% 1.64/0.59    inference(resolution,[],[f27,f31])).
% 1.64/0.59  fof(f31,plain,(
% 1.64/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f17])).
% 1.64/0.59  fof(f669,plain,(
% 1.64/0.59    ~r2_hidden(sK0,sK1) | ~spl5_3),
% 1.64/0.59    inference(subsumption_resolution,[],[f668,f28])).
% 1.64/0.59  fof(f668,plain,(
% 1.64/0.59    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK0,sK1) | ~spl5_3),
% 1.64/0.59    inference(subsumption_resolution,[],[f652,f44])).
% 1.64/0.59  fof(f44,plain,(
% 1.64/0.59    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.64/0.59    inference(equality_resolution,[],[f43])).
% 1.64/0.59  fof(f43,plain,(
% 1.64/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.64/0.59    inference(equality_resolution,[],[f34])).
% 1.64/0.59  fof(f34,plain,(
% 1.64/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.64/0.59    inference(cnf_transformation,[],[f21])).
% 1.64/0.59  fof(f652,plain,(
% 1.64/0.59    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK0,sK1) | ~spl5_3),
% 1.64/0.59    inference(duplicate_literal_removal,[],[f651])).
% 1.64/0.59  fof(f651,plain,(
% 1.64/0.59    ~r2_hidden(sK0,k1_tarski(sK0)) | k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) | ~r2_hidden(sK0,sK1) | ~r2_hidden(sK0,k1_tarski(sK0)) | ~spl5_3),
% 1.64/0.59    inference(superposition,[],[f42,f290])).
% 1.64/0.59  fof(f290,plain,(
% 1.64/0.59    sK0 = sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)) | ~spl5_3),
% 1.64/0.59    inference(resolution,[],[f145,f45])).
% 1.64/0.59  fof(f145,plain,(
% 1.64/0.59    r2_hidden(sK4(k1_tarski(sK0),sK1,k1_tarski(sK0)),k1_tarski(sK0)) | ~spl5_3),
% 1.64/0.59    inference(avatar_component_clause,[],[f143])).
% 1.64/0.59  fof(f42,plain,(
% 1.64/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 1.64/0.59    inference(cnf_transformation,[],[f26])).
% 1.64/0.59  % SZS output end Proof for theBenchmark
% 1.64/0.59  % (25197)------------------------------
% 1.64/0.59  % (25197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.59  % (25197)Termination reason: Refutation
% 1.64/0.59  
% 1.64/0.59  % (25197)Memory used [KB]: 11001
% 1.64/0.59  % (25197)Time elapsed: 0.148 s
% 1.64/0.59  % (25197)------------------------------
% 1.64/0.59  % (25197)------------------------------
% 1.64/0.59  % (25184)Success in time 0.232 s
%------------------------------------------------------------------------------
