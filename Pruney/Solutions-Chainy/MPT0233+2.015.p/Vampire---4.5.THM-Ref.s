%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:06 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   56 (  73 expanded)
%              Number of leaves         :   14 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 ( 233 expanded)
%              Number of equality atoms :   87 ( 113 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f84,f109,f177,f183])).

% (6313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f183,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl5_1
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f181,f73])).

fof(f73,plain,
    ( sK0 != sK3
    | spl5_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl5_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f181,plain,
    ( sK0 = sK3
    | spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f179,f78])).

fof(f78,plain,
    ( sK0 != sK2
    | spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f179,plain,
    ( sK0 = sK2
    | sK0 = sK3
    | ~ spl5_5 ),
    inference(resolution,[],[f176,f69])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f176,plain,
    ( r2_hidden(sK0,k2_tarski(sK2,sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl5_5
  <=> r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f177,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f163,f106,f174])).

fof(f106,plain,
    ( spl5_4
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f163,plain,
    ( r2_hidden(sK0,k2_tarski(sK2,sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f160,f108])).

fof(f108,plain,
    ( r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f160,plain,(
    ! [X12,X13] :
      ( ~ r1_tarski(k1_tarski(X13),X12)
      | r2_hidden(X13,X12) ) ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,(
    ! [X12,X13] :
      ( k1_tarski(X13) != k1_tarski(X13)
      | r2_hidden(X13,X12)
      | ~ r1_tarski(k1_tarski(X13),X12) ) ),
    inference(superposition,[],[f58,f92])).

fof(f92,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X5,X4) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f109,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f104,f81,f106])).

fof(f81,plain,
    ( spl5_3
  <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f104,plain,
    ( r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3))
    | ~ spl5_3 ),
    inference(resolution,[],[f99,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f99,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_tarski(sK0,sK1))
        | r1_tarski(X0,k2_tarski(sK2,sK3)) )
    | ~ spl5_3 ),
    inference(resolution,[],[f44,f83])).

fof(f83,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f84,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f37,f81])).

fof(f37,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

% (6308)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f79,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (6292)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.49  % (6285)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.49  % (6298)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (6289)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (6306)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (6314)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (6314)Refutation not found, incomplete strategy% (6314)------------------------------
% 0.20/0.51  % (6314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.51  % (6286)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.27/0.51  % (6314)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.51  
% 1.27/0.51  % (6314)Memory used [KB]: 1663
% 1.27/0.51  % (6314)Time elapsed: 0.002 s
% 1.27/0.51  % (6314)------------------------------
% 1.27/0.51  % (6314)------------------------------
% 1.27/0.52  % (6307)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.27/0.52  % (6302)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.52  % (6296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.27/0.52  % (6300)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.52  % (6287)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.27/0.52  % (6291)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.52  % (6288)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.27/0.52  % (6301)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.27/0.52  % (6306)Refutation found. Thanks to Tanya!
% 1.27/0.52  % SZS status Theorem for theBenchmark
% 1.27/0.52  % SZS output start Proof for theBenchmark
% 1.27/0.52  fof(f184,plain,(
% 1.27/0.52    $false),
% 1.27/0.52    inference(avatar_sat_refutation,[],[f74,f79,f84,f109,f177,f183])).
% 1.27/0.53  % (6313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  fof(f183,plain,(
% 1.27/0.53    spl5_1 | spl5_2 | ~spl5_5),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f182])).
% 1.27/0.53  fof(f182,plain,(
% 1.27/0.53    $false | (spl5_1 | spl5_2 | ~spl5_5)),
% 1.27/0.53    inference(subsumption_resolution,[],[f181,f73])).
% 1.27/0.53  fof(f73,plain,(
% 1.27/0.53    sK0 != sK3 | spl5_1),
% 1.27/0.53    inference(avatar_component_clause,[],[f71])).
% 1.27/0.53  fof(f71,plain,(
% 1.27/0.53    spl5_1 <=> sK0 = sK3),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.27/0.53  fof(f181,plain,(
% 1.27/0.53    sK0 = sK3 | (spl5_2 | ~spl5_5)),
% 1.27/0.53    inference(subsumption_resolution,[],[f179,f78])).
% 1.27/0.53  fof(f78,plain,(
% 1.27/0.53    sK0 != sK2 | spl5_2),
% 1.27/0.53    inference(avatar_component_clause,[],[f76])).
% 1.27/0.53  fof(f76,plain,(
% 1.27/0.53    spl5_2 <=> sK0 = sK2),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.27/0.53  fof(f179,plain,(
% 1.27/0.53    sK0 = sK2 | sK0 = sK3 | ~spl5_5),
% 1.27/0.53    inference(resolution,[],[f176,f69])).
% 1.27/0.53  fof(f69,plain,(
% 1.27/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.27/0.53    inference(equality_resolution,[],[f50])).
% 1.27/0.53  fof(f50,plain,(
% 1.27/0.53    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.27/0.53    inference(cnf_transformation,[],[f36])).
% 1.27/0.53  fof(f36,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 1.27/0.53  fof(f35,plain,(
% 1.27/0.53    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X1 & sK4(X0,X1,X2) != X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X1 | sK4(X0,X1,X2) = X0 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(rectify,[],[f33])).
% 1.27/0.53  fof(f33,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(flattening,[],[f32])).
% 1.27/0.53  fof(f32,plain,(
% 1.27/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.27/0.53    inference(nnf_transformation,[],[f11])).
% 1.27/0.53  fof(f11,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.27/0.53  fof(f176,plain,(
% 1.27/0.53    r2_hidden(sK0,k2_tarski(sK2,sK3)) | ~spl5_5),
% 1.27/0.53    inference(avatar_component_clause,[],[f174])).
% 1.27/0.53  fof(f174,plain,(
% 1.27/0.53    spl5_5 <=> r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.27/0.53  fof(f177,plain,(
% 1.27/0.53    spl5_5 | ~spl5_4),
% 1.27/0.53    inference(avatar_split_clause,[],[f163,f106,f174])).
% 1.27/0.53  fof(f106,plain,(
% 1.27/0.53    spl5_4 <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.27/0.53  fof(f163,plain,(
% 1.27/0.53    r2_hidden(sK0,k2_tarski(sK2,sK3)) | ~spl5_4),
% 1.27/0.53    inference(resolution,[],[f160,f108])).
% 1.27/0.53  fof(f108,plain,(
% 1.27/0.53    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3)) | ~spl5_4),
% 1.27/0.53    inference(avatar_component_clause,[],[f106])).
% 1.27/0.53  fof(f160,plain,(
% 1.27/0.53    ( ! [X12,X13] : (~r1_tarski(k1_tarski(X13),X12) | r2_hidden(X13,X12)) )),
% 1.27/0.53    inference(trivial_inequality_removal,[],[f159])).
% 1.27/0.53  fof(f159,plain,(
% 1.27/0.53    ( ! [X12,X13] : (k1_tarski(X13) != k1_tarski(X13) | r2_hidden(X13,X12) | ~r1_tarski(k1_tarski(X13),X12)) )),
% 1.27/0.53    inference(superposition,[],[f58,f92])).
% 1.27/0.53  fof(f92,plain,(
% 1.27/0.53    ( ! [X4,X5] : (k3_xboole_0(X5,X4) = X4 | ~r1_tarski(X4,X5)) )),
% 1.27/0.53    inference(superposition,[],[f40,f43])).
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f2])).
% 1.27/0.53  fof(f2,axiom,(
% 1.27/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.27/0.53  fof(f40,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f25])).
% 1.27/0.53  fof(f25,plain,(
% 1.27/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.27/0.53    inference(ennf_transformation,[],[f7])).
% 1.27/0.53  fof(f7,axiom,(
% 1.27/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.27/0.53  fof(f58,plain,(
% 1.27/0.53    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f28])).
% 1.27/0.53  fof(f28,plain,(
% 1.27/0.53    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.27/0.53    inference(ennf_transformation,[],[f20])).
% 1.27/0.53  fof(f20,axiom,(
% 1.27/0.53    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 1.27/0.53  fof(f109,plain,(
% 1.27/0.53    spl5_4 | ~spl5_3),
% 1.27/0.53    inference(avatar_split_clause,[],[f104,f81,f106])).
% 1.27/0.53  fof(f81,plain,(
% 1.27/0.53    spl5_3 <=> r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.27/0.53  fof(f104,plain,(
% 1.27/0.53    r1_tarski(k1_tarski(sK0),k2_tarski(sK2,sK3)) | ~spl5_3),
% 1.27/0.53    inference(resolution,[],[f99,f47])).
% 1.27/0.53  fof(f47,plain,(
% 1.27/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.27/0.53    inference(cnf_transformation,[],[f21])).
% 1.27/0.53  fof(f21,axiom,(
% 1.27/0.53    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.27/0.53  fof(f99,plain,(
% 1.27/0.53    ( ! [X0] : (~r1_tarski(X0,k2_tarski(sK0,sK1)) | r1_tarski(X0,k2_tarski(sK2,sK3))) ) | ~spl5_3),
% 1.27/0.53    inference(resolution,[],[f44,f83])).
% 1.27/0.53  fof(f83,plain,(
% 1.27/0.53    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) | ~spl5_3),
% 1.27/0.53    inference(avatar_component_clause,[],[f81])).
% 1.27/0.53  fof(f44,plain,(
% 1.27/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f27])).
% 1.27/0.53  fof(f27,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.27/0.53    inference(flattening,[],[f26])).
% 1.27/0.53  fof(f26,plain,(
% 1.27/0.53    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.27/0.53    inference(ennf_transformation,[],[f5])).
% 1.27/0.53  fof(f5,axiom,(
% 1.27/0.53    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.27/0.53  fof(f84,plain,(
% 1.27/0.53    spl5_3),
% 1.27/0.53    inference(avatar_split_clause,[],[f37,f81])).
% 1.27/0.53  fof(f37,plain,(
% 1.27/0.53    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.27/0.53    inference(cnf_transformation,[],[f30])).
% 1.27/0.53  fof(f30,plain,(
% 1.27/0.53    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f29])).
% 1.27/0.53  fof(f29,plain,(
% 1.27/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f24,plain,(
% 1.27/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.27/0.53    inference(ennf_transformation,[],[f23])).
% 1.27/0.53  fof(f23,negated_conjecture,(
% 1.27/0.53    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.27/0.53    inference(negated_conjecture,[],[f22])).
% 1.27/0.53  fof(f22,conjecture,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.27/0.53  % (6308)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.53  fof(f79,plain,(
% 1.27/0.53    ~spl5_2),
% 1.27/0.53    inference(avatar_split_clause,[],[f38,f76])).
% 1.27/0.53  fof(f38,plain,(
% 1.27/0.53    sK0 != sK2),
% 1.27/0.53    inference(cnf_transformation,[],[f30])).
% 1.27/0.53  fof(f74,plain,(
% 1.27/0.53    ~spl5_1),
% 1.27/0.53    inference(avatar_split_clause,[],[f39,f71])).
% 1.27/0.53  fof(f39,plain,(
% 1.27/0.53    sK0 != sK3),
% 1.27/0.53    inference(cnf_transformation,[],[f30])).
% 1.27/0.53  % SZS output end Proof for theBenchmark
% 1.27/0.53  % (6306)------------------------------
% 1.27/0.53  % (6306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (6306)Termination reason: Refutation
% 1.27/0.53  
% 1.27/0.53  % (6306)Memory used [KB]: 6268
% 1.27/0.53  % (6306)Time elapsed: 0.124 s
% 1.27/0.53  % (6306)------------------------------
% 1.27/0.53  % (6306)------------------------------
% 1.27/0.53  % (6312)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.53  % (6290)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.53  % (6284)Success in time 0.179 s
%------------------------------------------------------------------------------
