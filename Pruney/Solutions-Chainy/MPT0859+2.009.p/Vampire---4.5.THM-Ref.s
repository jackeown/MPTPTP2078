%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  88 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :  174 ( 301 expanded)
%              Number of equality atoms :   59 ( 116 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f54,f59,f66,f69,f92,f97])).

fof(f97,plain,
    ( spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl5_2
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f49,f91,f40])).

fof(f40,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f37])).

% (24050)Refutation not found, incomplete strategy% (24050)------------------------------
% (24050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24050)Termination reason: Refutation not found, incomplete strategy

% (24050)Memory used [KB]: 10618
% (24050)Time elapsed: 0.121 s
% (24050)------------------------------
% (24050)------------------------------
fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

% (24051)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

fof(f18,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

% (24051)Refutation not found, incomplete strategy% (24051)------------------------------
% (24051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24051)Termination reason: Refutation not found, incomplete strategy

% (24051)Memory used [KB]: 6140
% (24051)Time elapsed: 0.122 s
% (24051)------------------------------
% (24051)------------------------------
fof(f91,plain,
    ( r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_6
  <=> r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),k1_mcart_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f49,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f92,plain,
    ( spl5_4
    | spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f86,f63,f89,f56])).

fof(f56,plain,
    ( spl5_4
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f63,plain,
    ( spl5_5
  <=> r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f86,plain,
    ( r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | sK2 = k1_mcart_1(sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f80,f40])).

fof(f80,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,k2_tarski(k1_mcart_1(sK0),X2))
        | r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),X2)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f72,f65])).

fof(f65,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f63])).

% (24046)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (24026)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f72,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X4,k2_tarski(X6,X7))
      | r2_hidden(X7,k2_tarski(X4,X5))
      | r2_hidden(X6,k2_tarski(X4,X5)) ) ),
    inference(trivial_inequality_removal,[],[f71])).

fof(f71,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_tarski(X4,X5) != k2_tarski(X4,X5)
      | ~ r2_hidden(X4,k2_tarski(X6,X7))
      | r2_hidden(X7,k2_tarski(X4,X5))
      | r2_hidden(X6,k2_tarski(X4,X5)) ) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f69,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f53,f44,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f44,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f53,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl5_3
  <=> r2_hidden(k2_mcart_1(sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f66,plain,
    ( spl5_5
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f61,f42,f63])).

fof(f61,plain,
    ( r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))
    | ~ spl5_1 ),
    inference(resolution,[],[f23,f44])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,
    ( ~ spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f22,f51,f56])).

fof(f22,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK2 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
      | ( sK2 != k1_mcart_1(sK0)
        & sK1 != k1_mcart_1(sK0) ) )
    & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
          | ( k1_mcart_1(X0) != X2
            & k1_mcart_1(X0) != X1 ) )
        & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
        | ( sK2 != k1_mcart_1(sK0)
          & sK1 != k1_mcart_1(sK0) ) )
      & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X3)
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
       => ( r2_hidden(k2_mcart_1(X0),X3)
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))
     => ( r2_hidden(k2_mcart_1(X0),X3)
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

fof(f54,plain,
    ( ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f21,f51,f47])).

fof(f21,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK3)
    | sK1 != k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:45:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (24028)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (24033)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.51  % (24036)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (24030)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (24031)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (24027)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.51  % (24044)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (24027)Refutation not found, incomplete strategy% (24027)------------------------------
% 0.22/0.51  % (24027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24027)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24027)Memory used [KB]: 1663
% 0.22/0.51  % (24027)Time elapsed: 0.097 s
% 0.22/0.51  % (24027)------------------------------
% 0.22/0.51  % (24027)------------------------------
% 0.22/0.51  % (24036)Refutation not found, incomplete strategy% (24036)------------------------------
% 0.22/0.51  % (24036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24044)Refutation not found, incomplete strategy% (24044)------------------------------
% 0.22/0.51  % (24044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (24044)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24044)Memory used [KB]: 1663
% 0.22/0.51  % (24044)Time elapsed: 0.113 s
% 0.22/0.51  % (24044)------------------------------
% 0.22/0.51  % (24044)------------------------------
% 0.22/0.51  % (24036)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (24036)Memory used [KB]: 10746
% 0.22/0.51  % (24036)Time elapsed: 0.115 s
% 0.22/0.51  % (24036)------------------------------
% 0.22/0.51  % (24036)------------------------------
% 0.22/0.52  % (24040)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (24040)Refutation not found, incomplete strategy% (24040)------------------------------
% 0.22/0.52  % (24040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24040)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24040)Memory used [KB]: 1663
% 0.22/0.52  % (24040)Time elapsed: 0.077 s
% 0.22/0.52  % (24040)------------------------------
% 0.22/0.52  % (24040)------------------------------
% 0.22/0.52  % (24054)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.52  % (24029)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (24032)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (24041)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (24034)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (24048)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (24043)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (24049)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (24038)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (24047)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (24045)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (24050)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (24049)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f45,f54,f59,f66,f69,f92,f97])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl5_2 | ~spl5_6),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    $false | (spl5_2 | ~spl5_6)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f49,f91,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f37])).
% 0.22/0.53  % (24050)Refutation not found, incomplete strategy% (24050)------------------------------
% 0.22/0.53  % (24050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24050)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24050)Memory used [KB]: 10618
% 0.22/0.53  % (24050)Time elapsed: 0.121 s
% 0.22/0.53  % (24050)------------------------------
% 0.22/0.53  % (24050)------------------------------
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.53    inference(definition_unfolding,[],[f29,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  % (24051)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(rectify,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  % (24051)Refutation not found, incomplete strategy% (24051)------------------------------
% 0.22/0.53  % (24051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24051)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24051)Memory used [KB]: 6140
% 0.22/0.53  % (24051)Time elapsed: 0.122 s
% 0.22/0.53  % (24051)------------------------------
% 0.22/0.53  % (24051)------------------------------
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),k1_mcart_1(sK0))) | ~spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl5_6 <=> r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),k1_mcart_1(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    sK1 != k1_mcart_1(sK0) | spl5_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl5_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl5_4 | spl5_6 | ~spl5_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f86,f63,f89,f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    spl5_4 <=> sK2 = k1_mcart_1(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    spl5_5 <=> r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),k1_mcart_1(sK0))) | sK2 = k1_mcart_1(sK0) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f80,f40])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(sK2,k2_tarski(k1_mcart_1(sK0),X2)) | r2_hidden(sK1,k2_tarski(k1_mcart_1(sK0),X2))) ) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f72,f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) | ~spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f63])).
% 0.22/0.53  % (24046)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (24026)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k2_tarski(X6,X7)) | r2_hidden(X7,k2_tarski(X4,X5)) | r2_hidden(X6,k2_tarski(X4,X5))) )),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (k2_tarski(X4,X5) != k2_tarski(X4,X5) | ~r2_hidden(X4,k2_tarski(X6,X7)) | r2_hidden(X7,k2_tarski(X4,X5)) | r2_hidden(X6,k2_tarski(X4,X5))) )),
% 0.22/0.53    inference(superposition,[],[f26,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.22/0.53    inference(nnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ~spl5_1 | spl5_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    $false | (~spl5_1 | spl5_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f53,f44,f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    spl5_1 <=> r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ~r2_hidden(k2_mcart_1(sK0),sK3) | spl5_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl5_3 <=> r2_hidden(k2_mcart_1(sK0),sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    spl5_5 | ~spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f61,f42,f63])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    r2_hidden(k1_mcart_1(sK0),k2_tarski(sK1,sK2)) | ~spl5_1),
% 0.22/0.53    inference(resolution,[],[f23,f44])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ~spl5_4 | ~spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f22,f51,f56])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK2 != k1_mcart_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    (~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3))) => ((~r2_hidden(k2_mcart_1(sK0),sK3) | (sK2 != k1_mcart_1(sK0) & sK1 != k1_mcart_1(sK0))) & r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1,X2,X3] : ((~r2_hidden(k2_mcart_1(X0),X3) | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),X3)) => (r2_hidden(k2_mcart_1(X0),X3) & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ~spl5_2 | ~spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f51,f47])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ~r2_hidden(k2_mcart_1(sK0),sK3) | sK1 != k1_mcart_1(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl5_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f42])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (24049)------------------------------
% 0.22/0.53  % (24049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24039)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (24049)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (24049)Memory used [KB]: 10746
% 0.22/0.53  % (24049)Time elapsed: 0.120 s
% 0.22/0.53  % (24049)------------------------------
% 0.22/0.53  % (24049)------------------------------
% 0.22/0.53  % (24043)Refutation not found, incomplete strategy% (24043)------------------------------
% 0.22/0.53  % (24043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24043)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24043)Memory used [KB]: 1791
% 0.22/0.53  % (24043)Time elapsed: 0.123 s
% 0.22/0.53  % (24043)------------------------------
% 0.22/0.53  % (24043)------------------------------
% 0.22/0.53  % (24037)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (24052)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (24025)Success in time 0.17 s
%------------------------------------------------------------------------------
