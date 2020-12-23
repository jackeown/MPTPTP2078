%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 241 expanded)
%              Number of leaves         :    8 (  94 expanded)
%              Depth                    :   13
%              Number of atoms          :  154 ( 819 expanded)
%              Number of equality atoms :   54 ( 473 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f294,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f187,f293])).

fof(f293,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f283,f154])).

fof(f154,plain,(
    sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK2) ),
    inference(resolution,[],[f151,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f151,plain,(
    sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) ),
    inference(subsumption_resolution,[],[f150,f23])).

fof(f23,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f11,f20])).

fof(f11,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( sK2 = k2_mcart_1(sK2)
      | sK2 = k1_mcart_1(sK2) )
    & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8])).

fof(f8,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( k2_mcart_1(X2) = X2
              | k1_mcart_1(X2) = X2 )
            & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
   => ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X2] :
        ( ( k2_mcart_1(X2) = X2
          | k1_mcart_1(X2) = X2 )
        & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
   => ( ( sK2 = k2_mcart_1(sK2)
        | sK2 = k1_mcart_1(sK2) )
      & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( k2_mcart_1(X2) = X2
            | k1_mcart_1(X2) = X2 )
          & m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ~ ! [X2] :
                ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
               => ( k2_mcart_1(X2) != X2
                  & k1_mcart_1(X2) != X2 ) )
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => ( k2_mcart_1(X2) != X2
                & k1_mcart_1(X2) != X2 ) )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

fof(f150,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK0)
    | sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) ),
    inference(subsumption_resolution,[],[f148,f22])).

fof(f22,plain,(
    ~ sQ3_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f12,f20])).

fof(f12,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f148,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK1)
    | sQ3_eqProxy(k1_xboole_0,sK0)
    | sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) ),
    inference(resolution,[],[f47,f13])).

fof(f13,plain,(
    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k2_zfmisc_1(X1,X2))
      | sQ3_eqProxy(k1_xboole_0,X2)
      | sQ3_eqProxy(k1_xboole_0,X1)
      | sQ3_eqProxy(X0,k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0))) ) ),
    inference(resolution,[],[f26,f33])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)),X2)
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | sQ3_eqProxy(k1_xboole_0,X1)
      | sQ3_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f17,f20,f20,f20])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
      | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2
          | ~ m1_subset_1(X2,k2_zfmisc_1(X0,X1)) )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ~ ! [X2] :
              ( m1_subset_1(X2,k2_zfmisc_1(X0,X1))
             => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

fof(f283,plain,
    ( ~ sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f218,f155])).

fof(f155,plain,(
    ~ sQ3_eqProxy(sK2,k1_mcart_1(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))) ),
    inference(resolution,[],[f154,f54])).

fof(f54,plain,(
    ! [X6,X8,X7] :
      ( ~ sQ3_eqProxy(k4_tarski(X7,X8),X6)
      | ~ sQ3_eqProxy(X6,k1_mcart_1(k4_tarski(X7,X8))) ) ),
    inference(resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X2,X1] : ~ sQ3_eqProxy(k4_tarski(X1,X2),k1_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_proxy_replacement,[],[f19,f20])).

fof(f19,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 )
      | ! [X1,X2] : k4_tarski(X1,X2) != X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f218,plain,
    ( ! [X2] :
        ( sQ3_eqProxy(sK2,k1_mcart_1(X2))
        | ~ sQ3_eqProxy(X2,sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f188,f33])).

fof(f188,plain,
    ( ! [X0] :
        ( sQ3_eqProxy(k1_mcart_1(X0),sK2)
        | ~ sQ3_eqProxy(X0,sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f38,f83])).

fof(f83,plain,(
    ! [X17,X15,X16] :
      ( ~ sQ3_eqProxy(X15,k1_mcart_1(X16))
      | sQ3_eqProxy(k1_mcart_1(X17),X15)
      | ~ sQ3_eqProxy(X17,X16) ) ),
    inference(resolution,[],[f52,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_mcart_1(X1),k1_mcart_1(X0))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(resolution,[],[f28,f33])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k1_mcart_1(X0),k1_mcart_1(X1))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | ~ sQ3_eqProxy(X2,X0)
      | sQ3_eqProxy(X1,X2) ) ),
    inference(resolution,[],[f34,f33])).

fof(f38,plain,
    ( sQ3_eqProxy(sK2,k1_mcart_1(sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> sQ3_eqProxy(sK2,k1_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f187,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f179,f151])).

fof(f179,plain,
    ( ~ sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))
    | ~ spl4_2 ),
    inference(resolution,[],[f156,f114])).

fof(f114,plain,
    ( ! [X3] :
        ( sQ3_eqProxy(sK2,k2_mcart_1(X3))
        | ~ sQ3_eqProxy(sK2,X3) )
    | ~ spl4_2 ),
    inference(resolution,[],[f107,f33])).

fof(f107,plain,
    ( ! [X4] :
        ( sQ3_eqProxy(k2_mcart_1(X4),sK2)
        | ~ sQ3_eqProxy(sK2,X4) )
    | ~ spl4_2 ),
    inference(resolution,[],[f93,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k2_mcart_1(X1),k2_mcart_1(X0))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(resolution,[],[f29,f33])).

fof(f29,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k2_mcart_1(X0),k2_mcart_1(X1))
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f20])).

fof(f93,plain,
    ( ! [X3] :
        ( ~ sQ3_eqProxy(X3,k2_mcart_1(sK2))
        | sQ3_eqProxy(X3,sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f85,f33])).

fof(f85,plain,
    ( ! [X21] :
        ( sQ3_eqProxy(sK2,X21)
        | ~ sQ3_eqProxy(X21,k2_mcart_1(sK2)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,
    ( sQ3_eqProxy(k2_mcart_1(sK2),sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,
    ( sQ3_eqProxy(sK2,k2_mcart_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl4_2
  <=> sQ3_eqProxy(sK2,k2_mcart_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f156,plain,(
    ~ sQ3_eqProxy(sK2,k2_mcart_1(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))) ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X4,X5,X3] :
      ( ~ sQ3_eqProxy(k4_tarski(X4,X5),X3)
      | ~ sQ3_eqProxy(X3,k2_mcart_1(k4_tarski(X4,X5))) ) ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,(
    ! [X2,X1] : ~ sQ3_eqProxy(k4_tarski(X1,X2),k2_mcart_1(k4_tarski(X1,X2))) ),
    inference(equality_proxy_replacement,[],[f18,f20])).

fof(f18,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) != X0
      | k4_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f43,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f21,f40,f36])).

fof(f21,plain,
    ( sQ3_eqProxy(sK2,k2_mcart_1(sK2))
    | sQ3_eqProxy(sK2,k1_mcart_1(sK2)) ),
    inference(equality_proxy_replacement,[],[f14,f20,f20])).

fof(f14,plain,
    ( sK2 = k2_mcart_1(sK2)
    | sK2 = k1_mcart_1(sK2) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:33:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (21470)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (21473)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (21470)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (21478)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f43,f187,f293])).
% 0.21/0.48  fof(f293,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f292])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    $false | ~spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f283,f154])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK2)),
% 0.21/0.48    inference(resolution,[],[f151,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f151,plain,(
% 0.21/0.48    sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f150,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f11,f20])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k1_xboole_0 != sK0),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f9,f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0) => (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(sK0,sK1))) => ((sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)) & m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ? [X0,X1] : (? [X2] : ((k2_mcart_1(X2) = X2 | k1_mcart_1(X2) = X2) & m1_subset_1(X2,k2_zfmisc_1(X0,X1))) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    inference(negated_conjecture,[],[f3])).
% 0.21/0.48  fof(f3,conjecture,(
% 0.21/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => (k2_mcart_1(X2) != X2 & k1_mcart_1(X2) != X2)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    sQ3_eqProxy(k1_xboole_0,sK0) | sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k1_xboole_0,sK1)),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f12,f20])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    sQ3_eqProxy(k1_xboole_0,sK1) | sQ3_eqProxy(k1_xboole_0,sK0) | sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)))),
% 0.21/0.48    inference(resolution,[],[f47,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    m1_subset_1(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k2_zfmisc_1(X1,X2)) | sQ3_eqProxy(k1_xboole_0,X2) | sQ3_eqProxy(k1_xboole_0,X1) | sQ3_eqProxy(X0,k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)))) )),
% 0.21/0.48    inference(resolution,[],[f26,f33])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ3_eqProxy(k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)),X2) | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | sQ3_eqProxy(k1_xboole_0,X1) | sQ3_eqProxy(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f17,f20,f20,f20])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2 | ~m1_subset_1(X2,k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(~! [X2] : (m1_subset_1(X2,k2_zfmisc_1(X0,X1)) => k4_tarski(k1_mcart_1(X2),k2_mcart_1(X2)) = X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    ~sQ3_eqProxy(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2)),sK2) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f218,f155])).
% 0.21/0.48  fof(f155,plain,(
% 0.21/0.48    ~sQ3_eqProxy(sK2,k1_mcart_1(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))))),
% 0.21/0.48    inference(resolution,[],[f154,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X6,X8,X7] : (~sQ3_eqProxy(k4_tarski(X7,X8),X6) | ~sQ3_eqProxy(X6,k1_mcart_1(k4_tarski(X7,X8)))) )),
% 0.21/0.48    inference(resolution,[],[f34,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~sQ3_eqProxy(k4_tarski(X1,X2),k1_mcart_1(k4_tarski(X1,X2)))) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f19,f20])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k1_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ! [X0] : ((k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0) | ! [X1,X2] : k4_tarski(X1,X2) != X0)),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (sQ3_eqProxy(X0,X2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    ( ! [X2] : (sQ3_eqProxy(sK2,k1_mcart_1(X2)) | ~sQ3_eqProxy(X2,sK2)) ) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f188,f33])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k1_mcart_1(X0),sK2) | ~sQ3_eqProxy(X0,sK2)) ) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f38,f83])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ( ! [X17,X15,X16] : (~sQ3_eqProxy(X15,k1_mcart_1(X16)) | sQ3_eqProxy(k1_mcart_1(X17),X15) | ~sQ3_eqProxy(X17,X16)) )),
% 0.21/0.48    inference(resolution,[],[f52,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k1_mcart_1(X1),k1_mcart_1(X0)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f28,f33])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k1_mcart_1(X0),k1_mcart_1(X1)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sQ3_eqProxy(X0,X1) | ~sQ3_eqProxy(X2,X0) | sQ3_eqProxy(X1,X2)) )),
% 0.21/0.48    inference(resolution,[],[f34,f33])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    sQ3_eqProxy(sK2,k1_mcart_1(sK2)) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl4_1 <=> sQ3_eqProxy(sK2,k1_mcart_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ~spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    $false | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f151])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ~sQ3_eqProxy(sK2,k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f156,f114])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X3] : (sQ3_eqProxy(sK2,k2_mcart_1(X3)) | ~sQ3_eqProxy(sK2,X3)) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f107,f33])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X4] : (sQ3_eqProxy(k2_mcart_1(X4),sK2) | ~sQ3_eqProxy(sK2,X4)) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f93,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k2_mcart_1(X1),k2_mcart_1(X0)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f29,f33])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k2_mcart_1(X0),k2_mcart_1(X1)) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f20])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X3] : (~sQ3_eqProxy(X3,k2_mcart_1(sK2)) | sQ3_eqProxy(X3,sK2)) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f85,f33])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X21] : (sQ3_eqProxy(sK2,X21) | ~sQ3_eqProxy(X21,k2_mcart_1(sK2))) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f52,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    sQ3_eqProxy(k2_mcart_1(sK2),sK2) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f33,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    sQ3_eqProxy(sK2,k2_mcart_1(sK2)) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    spl4_2 <=> sQ3_eqProxy(sK2,k2_mcart_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ~sQ3_eqProxy(sK2,k2_mcart_1(k4_tarski(k1_mcart_1(sK2),k2_mcart_1(sK2))))),
% 0.21/0.48    inference(resolution,[],[f154,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~sQ3_eqProxy(k4_tarski(X4,X5),X3) | ~sQ3_eqProxy(X3,k2_mcart_1(k4_tarski(X4,X5)))) )),
% 0.21/0.48    inference(resolution,[],[f34,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~sQ3_eqProxy(k4_tarski(X1,X2),k2_mcart_1(k4_tarski(X1,X2)))) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f18,f20])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k4_tarski(X1,X2) != k2_mcart_1(k4_tarski(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_mcart_1(X0) != X0 | k4_tarski(X1,X2) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f40,f36])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    sQ3_eqProxy(sK2,k2_mcart_1(sK2)) | sQ3_eqProxy(sK2,k1_mcart_1(sK2))),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f14,f20,f20])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    sK2 = k2_mcart_1(sK2) | sK2 = k1_mcart_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21470)------------------------------
% 0.21/0.48  % (21470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21470)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21470)Memory used [KB]: 6140
% 0.21/0.48  % (21470)Time elapsed: 0.061 s
% 0.21/0.48  % (21470)------------------------------
% 0.21/0.48  % (21470)------------------------------
% 0.21/0.48  % (21464)Success in time 0.122 s
%------------------------------------------------------------------------------
