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
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 143 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :  211 ( 641 expanded)
%              Number of equality atoms :   15 (  58 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f182,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f42,f87,f88,f132,f149,f150,f152,f179,f181])).

fof(f181,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f120,f34,f84,f80])).

fof(f80,plain,
    ( spl5_3
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f84,plain,
    ( spl5_4
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f34,plain,
    ( spl5_1
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f120,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f36,f18])).

fof(f18,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != k5_xboole_0(sK1,sK2)
    & ! [X3] :
        ( ( ~ r2_hidden(X3,sK0)
          | ( ( ~ r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) )
            & ( r2_hidden(X3,sK2)
              | r2_hidden(X3,sK1) ) ) )
        & ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | r2_hidden(X3,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k5_xboole_0(X1,X2) != X0
        & ! [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) ) )
            & ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | r2_hidden(X3,X0) ) ) )
   => ( sK0 != k5_xboole_0(sK1,sK2)
      & ! [X3] :
          ( ( ~ r2_hidden(X3,sK0)
            | ( ( ~ r2_hidden(X3,sK2)
                | ~ r2_hidden(X3,sK1) )
              & ( r2_hidden(X3,sK2)
                | r2_hidden(X3,sK1) ) ) )
          & ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,sK2) )
              & ( r2_hidden(X3,sK2)
                | ~ r2_hidden(X3,sK1) ) )
            | r2_hidden(X3,sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) ) ) )
          & ( ( ( r2_hidden(X3,X1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) ) )
            | r2_hidden(X3,X0) ) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k5_xboole_0(X1,X2) != X0
      & ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,X0)
          <=> ( r2_hidden(X3,X1)
            <=> r2_hidden(X3,X2) ) )
       => k5_xboole_0(X1,X2) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,X0)
        <=> ( r2_hidden(X3,X1)
          <=> r2_hidden(X3,X2) ) )
     => k5_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).

fof(f36,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f179,plain,
    ( spl5_1
    | ~ spl5_4
    | spl5_3 ),
    inference(avatar_split_clause,[],[f174,f80,f84,f34])).

fof(f174,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | spl5_3 ),
    inference(resolution,[],[f81,f16])).

fof(f16,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK1)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f81,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f152,plain,
    ( ~ spl5_4
    | spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f127,f38,f80,f84])).

fof(f38,plain,
    ( spl5_2
  <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f127,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | spl5_2 ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f39,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f150,plain,
    ( spl5_3
    | ~ spl5_1
    | spl5_4 ),
    inference(avatar_split_clause,[],[f143,f84,f34,f80])).

fof(f143,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | spl5_4 ),
    inference(resolution,[],[f85,f17])).

fof(f17,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK0)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f85,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f149,plain,
    ( spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f144,f84,f80,f34])).

fof(f144,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)
    | spl5_4 ),
    inference(resolution,[],[f85,f15])).

fof(f15,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f132,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_2 ),
    inference(avatar_split_clause,[],[f126,f38,f84,f80])).

fof(f126,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | spl5_2 ),
    inference(resolution,[],[f39,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f74,f38,f84,f80])).

fof(f74,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f87,plain,
    ( spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f73,f38,f84,f80])).

fof(f73,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f40,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f42,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f32,f38,f34])).

fof(f32,plain,
    ( ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f21,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK3(X0,X1),X1)
      | ~ r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1),X1)
          | ~ r2_hidden(sK3(X0,X1),X0) )
        & ( r2_hidden(sK3(X0,X1),X1)
          | r2_hidden(sK3(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f27,plain,(
    ~ sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2)) ),
    inference(equality_proxy_replacement,[],[f19,f26])).

fof(f19,plain,(
    sK0 != k5_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f31,f38,f34])).

fof(f31,plain,
    ( r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))
    | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) ),
    inference(resolution,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f20,f26])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK3(X0,X1),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:59:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (22981)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.50  % (22988)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (22984)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (23000)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (22996)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (22992)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (22982)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (23008)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (22996)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 1.37/0.53  % (22985)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.53  % SZS output start Proof for theBenchmark
% 1.37/0.53  fof(f182,plain,(
% 1.37/0.53    $false),
% 1.37/0.53    inference(avatar_sat_refutation,[],[f41,f42,f87,f88,f132,f149,f150,f152,f179,f181])).
% 1.37/0.53  fof(f181,plain,(
% 1.37/0.53    ~spl5_3 | ~spl5_4 | ~spl5_1),
% 1.37/0.53    inference(avatar_split_clause,[],[f120,f34,f84,f80])).
% 1.37/0.53  fof(f80,plain,(
% 1.37/0.53    spl5_3 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.37/0.53  fof(f84,plain,(
% 1.37/0.53    spl5_4 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.37/0.53  fof(f34,plain,(
% 1.37/0.53    spl5_1 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.37/0.53  fof(f120,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | ~spl5_1),
% 1.37/0.53    inference(resolution,[],[f36,f18])).
% 1.37/0.53  fof(f18,plain,(
% 1.37/0.53    ( ! [X3] : (~r2_hidden(X3,sK0) | ~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f10])).
% 1.37/0.53  fof(f10,plain,(
% 1.37/0.53    sK0 != k5_xboole_0(sK1,sK2) & ! [X3] : ((~r2_hidden(X3,sK0) | ((~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,sK2) | r2_hidden(X3,sK1)))) & (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | r2_hidden(X3,sK0)))),
% 1.37/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 1.37/0.53  fof(f9,plain,(
% 1.37/0.53    ? [X0,X1,X2] : (k5_xboole_0(X1,X2) != X0 & ! [X3] : ((~r2_hidden(X3,X0) | ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)))) & (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | r2_hidden(X3,X0)))) => (sK0 != k5_xboole_0(sK1,sK2) & ! [X3] : ((~r2_hidden(X3,sK0) | ((~r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) & (r2_hidden(X3,sK2) | r2_hidden(X3,sK1)))) & (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | r2_hidden(X3,sK0))))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f8,plain,(
% 1.37/0.53    ? [X0,X1,X2] : (k5_xboole_0(X1,X2) != X0 & ! [X3] : ((~r2_hidden(X3,X0) | ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)))) & (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | r2_hidden(X3,X0))))),
% 1.37/0.53    inference(nnf_transformation,[],[f5])).
% 1.37/0.53  fof(f5,plain,(
% 1.37/0.53    ? [X0,X1,X2] : (k5_xboole_0(X1,X2) != X0 & ! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))))),
% 1.37/0.53    inference(ennf_transformation,[],[f4])).
% 1.37/0.53  fof(f4,negated_conjecture,(
% 1.37/0.53    ~! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 1.37/0.53    inference(negated_conjecture,[],[f3])).
% 1.37/0.53  fof(f3,conjecture,(
% 1.37/0.53    ! [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,X0) <=> (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => k5_xboole_0(X1,X2) = X0)),
% 1.37/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_0)).
% 1.37/0.53  fof(f36,plain,(
% 1.37/0.53    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) | ~spl5_1),
% 1.37/0.53    inference(avatar_component_clause,[],[f34])).
% 1.37/0.53  fof(f179,plain,(
% 1.37/0.53    spl5_1 | ~spl5_4 | spl5_3),
% 1.37/0.53    inference(avatar_split_clause,[],[f174,f80,f84,f34])).
% 1.37/0.53  fof(f174,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) | spl5_3),
% 1.37/0.53    inference(resolution,[],[f81,f16])).
% 1.37/0.53  fof(f16,plain,(
% 1.37/0.53    ( ! [X3] : (r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f10])).
% 1.37/0.53  fof(f81,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | spl5_3),
% 1.37/0.53    inference(avatar_component_clause,[],[f80])).
% 1.37/0.53  fof(f152,plain,(
% 1.37/0.53    ~spl5_4 | spl5_3 | spl5_2),
% 1.37/0.53    inference(avatar_split_clause,[],[f127,f38,f80,f84])).
% 1.37/0.53  fof(f38,plain,(
% 1.37/0.53    spl5_2 <=> r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2))),
% 1.37/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.37/0.53  fof(f127,plain,(
% 1.37/0.53    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | spl5_2),
% 1.37/0.53    inference(resolution,[],[f39,f25])).
% 1.37/0.53  fof(f25,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f14])).
% 1.37/0.53  fof(f14,plain,(
% 1.37/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.37/0.53    inference(nnf_transformation,[],[f7])).
% 1.37/0.53  fof(f7,plain,(
% 1.37/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.37/0.53    inference(ennf_transformation,[],[f1])).
% 1.37/0.53  fof(f1,axiom,(
% 1.37/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.37/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.37/0.53  fof(f39,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)) | spl5_2),
% 1.37/0.53    inference(avatar_component_clause,[],[f38])).
% 1.37/0.53  fof(f150,plain,(
% 1.37/0.53    spl5_3 | ~spl5_1 | spl5_4),
% 1.37/0.53    inference(avatar_split_clause,[],[f143,f84,f34,f80])).
% 1.37/0.53  fof(f143,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | spl5_4),
% 1.37/0.53    inference(resolution,[],[f85,f17])).
% 1.37/0.53  fof(f17,plain,(
% 1.37/0.53    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK0) | r2_hidden(X3,sK1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f10])).
% 1.37/0.53  fof(f85,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | spl5_4),
% 1.37/0.53    inference(avatar_component_clause,[],[f84])).
% 1.37/0.53  fof(f149,plain,(
% 1.37/0.53    spl5_1 | ~spl5_3 | spl5_4),
% 1.37/0.53    inference(avatar_split_clause,[],[f144,f84,f80,f34])).
% 1.37/0.53  fof(f144,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0) | spl5_4),
% 1.37/0.53    inference(resolution,[],[f85,f15])).
% 1.37/0.53  fof(f15,plain,(
% 1.37/0.53    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f10])).
% 1.37/0.53  fof(f132,plain,(
% 1.37/0.53    ~spl5_3 | spl5_4 | spl5_2),
% 1.37/0.53    inference(avatar_split_clause,[],[f126,f38,f84,f80])).
% 1.37/0.53  fof(f126,plain,(
% 1.37/0.53    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | spl5_2),
% 1.37/0.53    inference(resolution,[],[f39,f24])).
% 1.37/0.53  fof(f24,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f14])).
% 1.37/0.53  fof(f88,plain,(
% 1.37/0.53    ~spl5_3 | ~spl5_4 | ~spl5_2),
% 1.37/0.53    inference(avatar_split_clause,[],[f74,f38,f84,f80])).
% 1.37/0.53  fof(f74,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | ~spl5_2),
% 1.37/0.53    inference(resolution,[],[f40,f23])).
% 1.37/0.53  fof(f23,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f14])).
% 1.37/0.53  fof(f40,plain,(
% 1.37/0.53    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)) | ~spl5_2),
% 1.37/0.53    inference(avatar_component_clause,[],[f38])).
% 1.37/0.53  fof(f87,plain,(
% 1.37/0.53    spl5_3 | spl5_4 | ~spl5_2),
% 1.37/0.53    inference(avatar_split_clause,[],[f73,f38,f84,f80])).
% 1.37/0.53  fof(f73,plain,(
% 1.37/0.53    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK2) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK1) | ~spl5_2),
% 1.37/0.53    inference(resolution,[],[f40,f22])).
% 1.37/0.53  fof(f22,plain,(
% 1.37/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.37/0.53    inference(cnf_transformation,[],[f14])).
% 1.37/0.53  fof(f42,plain,(
% 1.37/0.53    ~spl5_1 | ~spl5_2),
% 1.37/0.53    inference(avatar_split_clause,[],[f32,f38,f34])).
% 1.37/0.53  fof(f32,plain,(
% 1.37/0.53    ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)) | ~r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)),
% 1.37/0.53    inference(resolution,[],[f27,f28])).
% 1.37/0.53  fof(f28,plain,(
% 1.37/0.53    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | ~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) )),
% 1.37/0.53    inference(equality_proxy_replacement,[],[f21,f26])).
% 1.37/0.53  fof(f26,plain,(
% 1.37/0.53    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 1.37/0.53    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 1.37/0.53  fof(f21,plain,(
% 1.37/0.53    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f13])).
% 1.37/0.53  fof(f13,plain,(
% 1.37/0.53    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.37/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f11,f12])).
% 1.37/0.53  fof(f12,plain,(
% 1.37/0.53    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK3(X0,X1),X1) | ~r2_hidden(sK3(X0,X1),X0)) & (r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0))))),
% 1.37/0.53    introduced(choice_axiom,[])).
% 1.37/0.53  fof(f11,plain,(
% 1.37/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.37/0.53    inference(nnf_transformation,[],[f6])).
% 1.37/0.53  fof(f6,plain,(
% 1.37/0.53    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.37/0.53    inference(ennf_transformation,[],[f2])).
% 1.37/0.53  fof(f2,axiom,(
% 1.37/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.37/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.37/0.53  fof(f27,plain,(
% 1.37/0.53    ~sQ4_eqProxy(sK0,k5_xboole_0(sK1,sK2))),
% 1.37/0.53    inference(equality_proxy_replacement,[],[f19,f26])).
% 1.37/0.53  fof(f19,plain,(
% 1.37/0.53    sK0 != k5_xboole_0(sK1,sK2)),
% 1.37/0.53    inference(cnf_transformation,[],[f10])).
% 1.37/0.53  fof(f41,plain,(
% 1.37/0.53    spl5_1 | spl5_2),
% 1.37/0.53    inference(avatar_split_clause,[],[f31,f38,f34])).
% 1.37/0.53  fof(f31,plain,(
% 1.37/0.53    r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),k5_xboole_0(sK1,sK2)) | r2_hidden(sK3(sK0,k5_xboole_0(sK1,sK2)),sK0)),
% 1.37/0.53    inference(resolution,[],[f27,f29])).
% 1.37/0.53  fof(f29,plain,(
% 1.37/0.53    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.37/0.53    inference(equality_proxy_replacement,[],[f20,f26])).
% 1.37/0.53  fof(f20,plain,(
% 1.37/0.53    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK3(X0,X1),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 1.37/0.53    inference(cnf_transformation,[],[f13])).
% 1.37/0.53  % SZS output end Proof for theBenchmark
% 1.37/0.53  % (22996)------------------------------
% 1.37/0.53  % (22996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.53  % (22996)Termination reason: Refutation
% 1.37/0.53  
% 1.37/0.53  % (22996)Memory used [KB]: 6268
% 1.37/0.53  % (22996)Time elapsed: 0.122 s
% 1.37/0.53  % (22996)------------------------------
% 1.37/0.53  % (22996)------------------------------
% 1.37/0.53  % (22986)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.53  % (22980)Success in time 0.174 s
%------------------------------------------------------------------------------
