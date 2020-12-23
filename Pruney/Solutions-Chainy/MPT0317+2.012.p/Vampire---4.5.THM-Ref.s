%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 124 expanded)
%              Number of leaves         :   10 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  175 ( 345 expanded)
%              Number of equality atoms :   50 ( 109 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f85,f86,f102,f105,f118,f121])).

fof(f121,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(resolution,[],[f107,f79])).

fof(f79,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f107,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f118,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(trivial_inequality_removal,[],[f116])).

fof(f116,plain,
    ( sK1 != sK1
    | ~ spl4_1
    | spl4_3 ),
    inference(superposition,[],[f83,f113])).

fof(f113,plain,
    ( sK1 = sK3
    | ~ spl4_1 ),
    inference(resolution,[],[f110,f106])).

fof(f106,plain,
    ( r2_hidden(sK1,k2_tarski(sK3,sK3))
    | ~ spl4_1 ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f110,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k2_tarski(X1,X1))
      | X1 = X2 ) ),
    inference(trivial_inequality_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X1] :
      ( k2_tarski(X1,X1) != k2_tarski(X1,X1)
      | ~ r2_hidden(X2,k2_tarski(X1,X1))
      | X1 = X2 ) ),
    inference(superposition,[],[f59,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f38,f32,f32,f32])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f35,f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f83,plain,
    ( sK1 != sK3
    | spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_3
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f105,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f101,f94])).

fof(f94,plain,(
    ! [X0] : r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( k2_tarski(X0,X0) != k2_tarski(X0,X0)
      | r2_hidden(X0,k2_tarski(X0,X0)) ) ),
    inference(superposition,[],[f67,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f36,f32])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f67,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f37,f32,f32,f32])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f101,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_4
  <=> r2_hidden(sK1,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f102,plain,
    ( ~ spl4_2
    | ~ spl4_4
    | spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f95,f81,f73,f99,f77])).

fof(f95,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ r2_hidden(sK0,sK2)
    | spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f49,f87])).

fof(f87,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1)))
    | spl4_1
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f75,f82])).

fof(f82,plain,
    ( sK1 = sK3
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f81])).

fof(f75,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f86,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f55,f77,f73])).

fof(f55,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f29,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( sK1 != sK3
      | ~ r2_hidden(sK0,sK2)
      | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
    & ( ( sK1 = sK3
        & r2_hidden(sK0,sK2) )
      | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | ~ r2_hidden(X0,X2)
          | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
        & ( ( X1 = X3
            & r2_hidden(X0,X2) )
          | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) )
   => ( ( sK1 != sK3
        | ~ r2_hidden(sK0,sK2)
        | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) )
      & ( ( sK1 = sK3
          & r2_hidden(sK0,sK2) )
        | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | ~ r2_hidden(X0,X2)
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <~> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
      <=> ( X1 = X3
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

fof(f85,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f54,f81,f73])).

fof(f54,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,
    ( sK1 = sK3
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f81,f77,f73])).

fof(f53,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f31,plain,
    ( sK1 != sK3
    | ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:12:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.55  % (30979)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.56  % (30977)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.56  % (30979)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % (30968)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.57  % (30972)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.57  % (30984)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.57  % (30990)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.57  % (30997)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.58  % (30989)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.58  % SZS output start Proof for theBenchmark
% 0.19/0.58  fof(f122,plain,(
% 0.19/0.58    $false),
% 0.19/0.58    inference(avatar_sat_refutation,[],[f84,f85,f86,f102,f105,f118,f121])).
% 0.19/0.58  fof(f121,plain,(
% 0.19/0.58    ~spl4_1 | spl4_2),
% 0.19/0.58    inference(avatar_contradiction_clause,[],[f120])).
% 0.19/0.58  fof(f120,plain,(
% 0.19/0.58    $false | (~spl4_1 | spl4_2)),
% 0.19/0.58    inference(resolution,[],[f107,f79])).
% 0.19/0.58  fof(f79,plain,(
% 0.19/0.58    ~r2_hidden(sK0,sK2) | spl4_2),
% 0.19/0.58    inference(avatar_component_clause,[],[f77])).
% 0.19/0.58  fof(f77,plain,(
% 0.19/0.58    spl4_2 <=> r2_hidden(sK0,sK2)),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.58  fof(f107,plain,(
% 0.19/0.58    r2_hidden(sK0,sK2) | ~spl4_1),
% 0.19/0.58    inference(resolution,[],[f74,f47])).
% 0.19/0.58  fof(f47,plain,(
% 0.19/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f26])).
% 0.19/0.58  fof(f26,plain,(
% 0.19/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.58    inference(flattening,[],[f25])).
% 0.19/0.58  fof(f25,plain,(
% 0.19/0.58    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 0.19/0.58    inference(nnf_transformation,[],[f4])).
% 0.19/0.58  fof(f4,axiom,(
% 0.19/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.19/0.58  fof(f74,plain,(
% 0.19/0.58    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) | ~spl4_1),
% 0.19/0.58    inference(avatar_component_clause,[],[f73])).
% 0.19/0.58  fof(f73,plain,(
% 0.19/0.58    spl4_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.58  fof(f118,plain,(
% 0.19/0.58    ~spl4_1 | spl4_3),
% 0.19/0.58    inference(avatar_contradiction_clause,[],[f117])).
% 0.19/0.58  fof(f117,plain,(
% 0.19/0.58    $false | (~spl4_1 | spl4_3)),
% 0.19/0.58    inference(trivial_inequality_removal,[],[f116])).
% 0.19/0.58  fof(f116,plain,(
% 0.19/0.58    sK1 != sK1 | (~spl4_1 | spl4_3)),
% 0.19/0.58    inference(superposition,[],[f83,f113])).
% 0.19/0.58  fof(f113,plain,(
% 0.19/0.58    sK1 = sK3 | ~spl4_1),
% 0.19/0.58    inference(resolution,[],[f110,f106])).
% 0.19/0.58  fof(f106,plain,(
% 0.19/0.58    r2_hidden(sK1,k2_tarski(sK3,sK3)) | ~spl4_1),
% 0.19/0.58    inference(resolution,[],[f74,f48])).
% 0.19/0.58  fof(f48,plain,(
% 0.19/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f26])).
% 0.19/0.58  fof(f110,plain,(
% 0.19/0.58    ( ! [X2,X1] : (~r2_hidden(X2,k2_tarski(X1,X1)) | X1 = X2) )),
% 0.19/0.58    inference(trivial_inequality_removal,[],[f109])).
% 0.19/0.58  fof(f109,plain,(
% 0.19/0.58    ( ! [X2,X1] : (k2_tarski(X1,X1) != k2_tarski(X1,X1) | ~r2_hidden(X2,k2_tarski(X1,X1)) | X1 = X2) )),
% 0.19/0.58    inference(superposition,[],[f59,f60])).
% 0.19/0.58  fof(f60,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) | X0 = X1) )),
% 0.19/0.58    inference(definition_unfolding,[],[f38,f32,f32,f32])).
% 0.19/0.58  fof(f32,plain,(
% 0.19/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f1])).
% 0.19/0.58  fof(f1,axiom,(
% 0.19/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.58  fof(f38,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.19/0.58    inference(cnf_transformation,[],[f22])).
% 0.19/0.58  fof(f22,plain,(
% 0.19/0.58    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.19/0.58    inference(nnf_transformation,[],[f6])).
% 0.19/0.58  fof(f6,axiom,(
% 0.19/0.58    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.58  fof(f59,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.19/0.58    inference(definition_unfolding,[],[f35,f32])).
% 0.19/0.58  fof(f35,plain,(
% 0.19/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.19/0.58    inference(cnf_transformation,[],[f21])).
% 0.19/0.58  fof(f21,plain,(
% 0.19/0.58    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.19/0.58    inference(nnf_transformation,[],[f9])).
% 0.19/0.58  fof(f9,axiom,(
% 0.19/0.58    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.58  fof(f83,plain,(
% 0.19/0.58    sK1 != sK3 | spl4_3),
% 0.19/0.58    inference(avatar_component_clause,[],[f81])).
% 0.19/0.58  fof(f81,plain,(
% 0.19/0.58    spl4_3 <=> sK1 = sK3),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.58  fof(f105,plain,(
% 0.19/0.58    spl4_4),
% 0.19/0.58    inference(avatar_contradiction_clause,[],[f103])).
% 0.19/0.58  fof(f103,plain,(
% 0.19/0.58    $false | spl4_4),
% 0.19/0.58    inference(resolution,[],[f101,f94])).
% 0.19/0.58  fof(f94,plain,(
% 0.19/0.58    ( ! [X0] : (r2_hidden(X0,k2_tarski(X0,X0))) )),
% 0.19/0.58    inference(trivial_inequality_removal,[],[f93])).
% 0.19/0.58  fof(f93,plain,(
% 0.19/0.58    ( ! [X0] : (k2_tarski(X0,X0) != k2_tarski(X0,X0) | r2_hidden(X0,k2_tarski(X0,X0))) )),
% 0.19/0.58    inference(superposition,[],[f67,f58])).
% 0.19/0.58  fof(f58,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.19/0.58    inference(definition_unfolding,[],[f36,f32])).
% 0.19/0.58  fof(f36,plain,(
% 0.19/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f21])).
% 0.19/0.58  fof(f67,plain,(
% 0.19/0.58    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 0.19/0.58    inference(equality_resolution,[],[f61])).
% 0.19/0.58  fof(f61,plain,(
% 0.19/0.58    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 0.19/0.58    inference(definition_unfolding,[],[f37,f32,f32,f32])).
% 0.19/0.58  fof(f37,plain,(
% 0.19/0.58    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.58    inference(cnf_transformation,[],[f22])).
% 0.19/0.58  fof(f101,plain,(
% 0.19/0.58    ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | spl4_4),
% 0.19/0.58    inference(avatar_component_clause,[],[f99])).
% 0.19/0.58  fof(f99,plain,(
% 0.19/0.58    spl4_4 <=> r2_hidden(sK1,k2_tarski(sK1,sK1))),
% 0.19/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.58  fof(f102,plain,(
% 0.19/0.58    ~spl4_2 | ~spl4_4 | spl4_1 | ~spl4_3),
% 0.19/0.58    inference(avatar_split_clause,[],[f95,f81,f73,f99,f77])).
% 0.19/0.58  fof(f95,plain,(
% 0.19/0.58    ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | ~r2_hidden(sK0,sK2) | (spl4_1 | ~spl4_3)),
% 0.19/0.58    inference(resolution,[],[f49,f87])).
% 0.19/0.58  fof(f87,plain,(
% 0.19/0.58    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK1,sK1))) | (spl4_1 | ~spl4_3)),
% 0.19/0.58    inference(forward_demodulation,[],[f75,f82])).
% 0.19/0.58  fof(f82,plain,(
% 0.19/0.58    sK1 = sK3 | ~spl4_3),
% 0.19/0.58    inference(avatar_component_clause,[],[f81])).
% 0.19/0.58  fof(f75,plain,(
% 0.19/0.58    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3))) | spl4_1),
% 0.19/0.58    inference(avatar_component_clause,[],[f73])).
% 0.19/0.58  fof(f49,plain,(
% 0.19/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 0.19/0.58    inference(cnf_transformation,[],[f26])).
% 0.19/0.58  fof(f86,plain,(
% 0.19/0.58    spl4_1 | spl4_2),
% 0.19/0.58    inference(avatar_split_clause,[],[f55,f77,f73])).
% 0.19/0.58  fof(f55,plain,(
% 0.19/0.58    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.19/0.58    inference(definition_unfolding,[],[f29,f32])).
% 0.19/0.58  fof(f29,plain,(
% 0.19/0.58    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.19/0.58    inference(cnf_transformation,[],[f19])).
% 0.19/0.58  fof(f19,plain,(
% 0.19/0.58    (sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3))))),
% 0.19/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 0.19/0.58  fof(f18,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))))) => ((sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))) & ((sK1 = sK3 & r2_hidden(sK0,sK2)) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))))),
% 0.19/0.58    introduced(choice_axiom,[])).
% 0.19/0.58  fof(f17,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3] : ((X1 != X3 | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.19/0.58    inference(flattening,[],[f16])).
% 0.19/0.58  fof(f16,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3] : (((X1 != X3 | ~r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) & ((X1 = X3 & r2_hidden(X0,X2)) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 0.19/0.58    inference(nnf_transformation,[],[f12])).
% 0.19/0.58  fof(f12,plain,(
% 0.19/0.58    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <~> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.19/0.58    inference(ennf_transformation,[],[f11])).
% 0.19/0.58  fof(f11,negated_conjecture,(
% 0.19/0.58    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.19/0.58    inference(negated_conjecture,[],[f10])).
% 0.19/0.58  fof(f10,conjecture,(
% 0.19/0.58    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 0.19/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).
% 0.19/0.58  fof(f85,plain,(
% 0.19/0.58    spl4_1 | spl4_3),
% 0.19/0.58    inference(avatar_split_clause,[],[f54,f81,f73])).
% 0.19/0.58  fof(f54,plain,(
% 0.19/0.58    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.19/0.58    inference(definition_unfolding,[],[f30,f32])).
% 0.19/0.58  fof(f30,plain,(
% 0.19/0.58    sK1 = sK3 | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.19/0.58    inference(cnf_transformation,[],[f19])).
% 0.19/0.58  fof(f84,plain,(
% 0.19/0.58    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.19/0.58    inference(avatar_split_clause,[],[f53,f81,f77,f73])).
% 0.19/0.58  fof(f53,plain,(
% 0.19/0.58    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k2_tarski(sK3,sK3)))),
% 0.19/0.58    inference(definition_unfolding,[],[f31,f32])).
% 0.19/0.58  fof(f31,plain,(
% 0.19/0.58    sK1 != sK3 | ~r2_hidden(sK0,sK2) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,k1_tarski(sK3)))),
% 0.19/0.58    inference(cnf_transformation,[],[f19])).
% 0.19/0.58  % SZS output end Proof for theBenchmark
% 0.19/0.58  % (30979)------------------------------
% 0.19/0.58  % (30979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.58  % (30979)Termination reason: Refutation
% 0.19/0.58  
% 0.19/0.58  % (30979)Memory used [KB]: 6268
% 0.19/0.58  % (30979)Time elapsed: 0.152 s
% 0.19/0.58  % (30979)------------------------------
% 0.19/0.58  % (30979)------------------------------
% 0.19/0.58  % (30988)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.58  % (30973)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.58  % (30962)Success in time 0.232 s
%------------------------------------------------------------------------------
