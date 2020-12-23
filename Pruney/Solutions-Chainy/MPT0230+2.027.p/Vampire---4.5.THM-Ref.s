%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 (  94 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 ( 332 expanded)
%              Number of equality atoms :  100 ( 178 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f251,f257,f264,f287])).

fof(f287,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f279,f121])).

% (22498)Refutation not found, incomplete strategy% (22498)------------------------------
% (22498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f121,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f120,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f120,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( X0 != X0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f54,f62])).

fof(f62,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f279,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl5_9 ),
    inference(superposition,[],[f108,f250])).

fof(f250,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl5_9
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f108,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f82,f61])).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f82,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f264,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | spl5_1
    | spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f262,f96])).

fof(f96,plain,
    ( sK0 != sK2
    | spl5_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f262,plain,
    ( sK0 = sK2
    | spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f260,f101])).

fof(f101,plain,
    ( sK0 != sK1
    | spl5_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f260,plain,
    ( sK0 = sK1
    | sK0 = sK2
    | ~ spl5_10 ),
    inference(resolution,[],[f256,f83])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f256,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl5_10
  <=> r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f257,plain,
    ( spl5_10
    | spl5_8 ),
    inference(avatar_split_clause,[],[f252,f244,f254])).

fof(f244,plain,
    ( spl5_8
  <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f252,plain,
    ( r2_hidden(sK0,k2_tarski(sK1,sK2))
    | spl5_8 ),
    inference(resolution,[],[f246,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f246,plain,
    ( ~ r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f244])).

fof(f251,plain,
    ( ~ spl5_8
    | spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f240,f104,f248,f244])).

fof(f104,plain,
    ( spl5_3
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f240,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f122,f106])).

fof(f106,plain,
    ( r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f122,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X2
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f58,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f107,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f42,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK0 != sK2
    & sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) )
   => ( sK0 != sK2
      & sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f102,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f43,f99])).

fof(f43,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f27])).

fof(f97,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f44,f94])).

fof(f44,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:21:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (22471)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (22500)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (22492)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (22476)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (22487)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (22479)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (22482)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (22477)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (22474)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (22472)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (22472)Refutation not found, incomplete strategy% (22472)------------------------------
% 0.21/0.54  % (22472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22472)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22472)Memory used [KB]: 1663
% 0.21/0.54  % (22472)Time elapsed: 0.093 s
% 0.21/0.54  % (22472)------------------------------
% 0.21/0.54  % (22472)------------------------------
% 0.21/0.54  % (22495)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (22483)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (22497)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (22486)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (22500)Refutation not found, incomplete strategy% (22500)------------------------------
% 0.21/0.54  % (22500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22500)Memory used [KB]: 1663
% 0.21/0.54  % (22500)Time elapsed: 0.133 s
% 0.21/0.54  % (22500)------------------------------
% 0.21/0.54  % (22500)------------------------------
% 0.21/0.55  % (22485)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (22496)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (22488)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (22495)Refutation not found, incomplete strategy% (22495)------------------------------
% 0.21/0.55  % (22495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22495)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22495)Memory used [KB]: 10746
% 0.21/0.55  % (22495)Time elapsed: 0.093 s
% 0.21/0.55  % (22495)------------------------------
% 0.21/0.55  % (22495)------------------------------
% 0.21/0.55  % (22488)Refutation not found, incomplete strategy% (22488)------------------------------
% 0.21/0.55  % (22488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22493)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (22485)Refutation not found, incomplete strategy% (22485)------------------------------
% 0.21/0.55  % (22485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22485)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22485)Memory used [KB]: 1791
% 0.21/0.55  % (22485)Time elapsed: 0.147 s
% 0.21/0.55  % (22485)------------------------------
% 0.21/0.55  % (22485)------------------------------
% 0.21/0.55  % (22475)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (22494)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (22487)Refutation not found, incomplete strategy% (22487)------------------------------
% 0.21/0.55  % (22487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22487)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22487)Memory used [KB]: 10618
% 0.21/0.55  % (22487)Time elapsed: 0.131 s
% 0.21/0.55  % (22487)------------------------------
% 0.21/0.55  % (22487)------------------------------
% 0.21/0.55  % (22480)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (22498)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (22478)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (22492)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f288,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f97,f102,f107,f251,f257,f264,f287])).
% 0.21/0.56  fof(f287,plain,(
% 0.21/0.56    ~spl5_9),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f286])).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    $false | ~spl5_9),
% 0.21/0.56    inference(subsumption_resolution,[],[f279,f121])).
% 0.21/0.56  % (22498)Refutation not found, incomplete strategy% (22498)------------------------------
% 0.21/0.56  % (22498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(resolution,[],[f120,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ( ! [X0] : (X0 != X0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.56    inference(superposition,[],[f54,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.56  fof(f279,plain,(
% 0.21/0.56    r2_hidden(sK0,k1_xboole_0) | ~spl5_9),
% 0.21/0.56    inference(superposition,[],[f108,f250])).
% 0.21/0.56  fof(f250,plain,(
% 0.21/0.56    k1_xboole_0 = k1_tarski(sK0) | ~spl5_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f248])).
% 0.21/0.56  fof(f248,plain,(
% 0.21/0.56    spl5_9 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.56    inference(superposition,[],[f82,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X4,X1] : (r2_hidden(X4,k2_tarski(X4,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_tarski(X4,X1) != X2) )),
% 0.21/0.56    inference(equality_resolution,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(rectify,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(flattening,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.56  fof(f264,plain,(
% 0.21/0.56    spl5_1 | spl5_2 | ~spl5_10),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f263])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    $false | (spl5_1 | spl5_2 | ~spl5_10)),
% 0.21/0.56    inference(subsumption_resolution,[],[f262,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    sK0 != sK2 | spl5_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    spl5_1 <=> sK0 = sK2),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.56  fof(f262,plain,(
% 0.21/0.56    sK0 = sK2 | (spl5_2 | ~spl5_10)),
% 0.21/0.56    inference(subsumption_resolution,[],[f260,f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    sK0 != sK1 | spl5_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    spl5_2 <=> sK0 = sK1),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.56  fof(f260,plain,(
% 0.21/0.56    sK0 = sK1 | sK0 = sK2 | ~spl5_10),
% 0.21/0.56    inference(resolution,[],[f256,f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.21/0.56    inference(equality_resolution,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f32])).
% 0.21/0.56  fof(f256,plain,(
% 0.21/0.56    r2_hidden(sK0,k2_tarski(sK1,sK2)) | ~spl5_10),
% 0.21/0.56    inference(avatar_component_clause,[],[f254])).
% 0.21/0.56  fof(f254,plain,(
% 0.21/0.56    spl5_10 <=> r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.56  fof(f257,plain,(
% 0.21/0.56    spl5_10 | spl5_8),
% 0.21/0.56    inference(avatar_split_clause,[],[f252,f244,f254])).
% 0.21/0.56  fof(f244,plain,(
% 0.21/0.56    spl5_8 <=> r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.56  fof(f252,plain,(
% 0.21/0.56    r2_hidden(sK0,k2_tarski(sK1,sK2)) | spl5_8),
% 0.21/0.56    inference(resolution,[],[f246,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,axiom,(
% 0.21/0.56    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 0.21/0.56  fof(f246,plain,(
% 0.21/0.56    ~r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) | spl5_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f244])).
% 0.21/0.56  fof(f251,plain,(
% 0.21/0.56    ~spl5_8 | spl5_9 | ~spl5_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f240,f104,f248,f244])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    spl5_3 <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    k1_xboole_0 = k1_tarski(sK0) | ~r1_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl5_3),
% 0.21/0.56    inference(resolution,[],[f122,f106])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) | ~spl5_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f104])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k1_xboole_0 = X2 | ~r1_xboole_0(X2,X3)) )),
% 0.21/0.56    inference(superposition,[],[f58,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.56    inference(nnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl5_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f42,f104])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) => (sK0 != sK2 & sK0 != sK1 & r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.56    inference(negated_conjecture,[],[f19])).
% 0.21/0.56  fof(f19,conjecture,(
% 0.21/0.56    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ~spl5_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f43,f99])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    sK0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ~spl5_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f44,f94])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    sK0 != sK2),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (22492)------------------------------
% 0.21/0.56  % (22492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22492)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (22492)Memory used [KB]: 6396
% 0.21/0.56  % (22492)Time elapsed: 0.132 s
% 0.21/0.56  % (22492)------------------------------
% 0.21/0.56  % (22492)------------------------------
% 0.21/0.56  % (22470)Success in time 0.188 s
%------------------------------------------------------------------------------
