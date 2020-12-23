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
% DateTime   : Thu Dec  3 12:35:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 (  98 expanded)
%              Number of leaves         :   16 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  187 ( 313 expanded)
%              Number of equality atoms :   68 ( 133 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f75,f103,f123,f136,f139,f147])).

fof(f147,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl4_1
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f144,f56])).

fof(f56,plain,
    ( sK0 != sK1
    | spl4_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,
    ( sK0 = sK1
    | ~ spl4_7 ),
    inference(resolution,[],[f102,f50])).

fof(f50,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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

fof(f102,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_7
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f139,plain,
    ( spl4_5
    | ~ spl4_2
    | spl4_6 ),
    inference(avatar_split_clause,[],[f138,f89,f59,f85])).

fof(f85,plain,
    ( spl4_5
  <=> k1_tarski(sK0) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f59,plain,
    ( spl4_2
  <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f89,plain,
    ( spl4_6
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f138,plain,
    ( k1_tarski(sK0) = k1_tarski(sK1)
    | ~ spl4_2
    | spl4_6 ),
    inference(subsumption_resolution,[],[f137,f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_tarski(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f137,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | k1_tarski(sK0) = k1_tarski(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f61,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f136,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f37,f71,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f71,plain,
    ( ! [X2,X1] : ~ r1_xboole_0(X1,X2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_3
  <=> ! [X1,X2] : ~ r1_xboole_0(X1,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f123,plain,
    ( ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f114,f74])).

fof(f74,plain,
    ( ! [X3] : ~ r2_hidden(X3,k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl4_4
  <=> ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f114,plain,
    ( r2_hidden(sK0,k1_xboole_0)
    | ~ spl4_6 ),
    inference(superposition,[],[f49,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f49,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,
    ( spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f98,f85,f100])).

fof(f98,plain,
    ( r2_hidden(sK1,k1_tarski(sK0))
    | ~ spl4_5 ),
    inference(superposition,[],[f49,f87])).

fof(f87,plain,
    ( k1_tarski(sK0) = k1_tarski(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f75,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f68,f73,f70])).

fof(f68,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

% (10466)Refutation not found, incomplete strategy% (10466)------------------------------
% (10466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10466)Termination reason: Refutation not found, incomplete strategy

% (10466)Memory used [KB]: 6268
% (10466)Time elapsed: 0.117 s
% (10466)------------------------------
% (10466)------------------------------
fof(f62,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( sK0 != sK1
    & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & r1_tarski(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f57,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (10448)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (10450)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (10466)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (10458)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (10444)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (10442)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (10469)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (10461)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (10443)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (10469)Refutation not found, incomplete strategy% (10469)------------------------------
% 0.20/0.54  % (10469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10469)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10469)Memory used [KB]: 1663
% 0.20/0.54  % (10469)Time elapsed: 0.004 s
% 0.20/0.54  % (10469)------------------------------
% 0.20/0.54  % (10469)------------------------------
% 0.20/0.54  % (10440)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.54  % (10441)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.54  % (10441)Refutation not found, incomplete strategy% (10441)------------------------------
% 0.20/0.54  % (10441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10441)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10441)Memory used [KB]: 1663
% 0.20/0.54  % (10441)Time elapsed: 0.126 s
% 0.20/0.54  % (10441)------------------------------
% 0.20/0.54  % (10441)------------------------------
% 0.20/0.54  % (10447)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.54  % (10467)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.54  % (10446)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (10461)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (10445)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f57,f62,f75,f103,f123,f136,f139,f147])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    spl4_1 | ~spl4_7),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f146])).
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    $false | (spl4_1 | ~spl4_7)),
% 0.20/0.54    inference(subsumption_resolution,[],[f144,f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    sK0 != sK1 | spl4_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f54])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    spl4_1 <=> sK0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.54  fof(f144,plain,(
% 0.20/0.54    sK0 = sK1 | ~spl4_7),
% 0.20/0.54    inference(resolution,[],[f102,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.54    inference(equality_resolution,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.54    inference(rectify,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.54  fof(f102,plain,(
% 0.20/0.54    r2_hidden(sK1,k1_tarski(sK0)) | ~spl4_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f100])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    spl4_7 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.54  fof(f139,plain,(
% 0.20/0.54    spl4_5 | ~spl4_2 | spl4_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f138,f89,f59,f85])).
% 0.20/0.54  fof(f85,plain,(
% 0.20/0.54    spl4_5 <=> k1_tarski(sK0) = k1_tarski(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl4_2 <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    spl4_6 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    k1_tarski(sK0) = k1_tarski(sK1) | (~spl4_2 | spl4_6)),
% 0.20/0.54    inference(subsumption_resolution,[],[f137,f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    k1_xboole_0 != k1_tarski(sK0) | spl4_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f89])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    k1_xboole_0 = k1_tarski(sK0) | k1_tarski(sK0) = k1_tarski(sK1) | ~spl4_2),
% 0.20/0.54    inference(resolution,[],[f61,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | ~spl4_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f59])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    ~spl4_3),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    $false | ~spl4_3),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f37,f71,f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~r1_xboole_0(X1,X2)) ) | ~spl4_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    spl4_3 <=> ! [X1,X2] : ~r1_xboole_0(X1,X2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.54    inference(rectify,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.54  fof(f123,plain,(
% 0.20/0.54    ~spl4_4 | ~spl4_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f122])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    $false | (~spl4_4 | ~spl4_6)),
% 0.20/0.54    inference(subsumption_resolution,[],[f114,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) ) | ~spl4_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    spl4_4 <=> ! [X3] : ~r2_hidden(X3,k1_xboole_0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.54  fof(f114,plain,(
% 0.20/0.54    r2_hidden(sK0,k1_xboole_0) | ~spl4_6),
% 0.20/0.54    inference(superposition,[],[f49,f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    k1_xboole_0 = k1_tarski(sK0) | ~spl4_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f89])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.20/0.54    inference(equality_resolution,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.20/0.54    inference(equality_resolution,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    spl4_7 | ~spl4_5),
% 0.20/0.54    inference(avatar_split_clause,[],[f98,f85,f100])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    r2_hidden(sK1,k1_tarski(sK0)) | ~spl4_5),
% 0.20/0.54    inference(superposition,[],[f49,f87])).
% 0.20/0.54  fof(f87,plain,(
% 0.20/0.54    k1_tarski(sK0) = k1_tarski(sK1) | ~spl4_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f85])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    spl4_3 | spl4_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f68,f73,f70])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X2,X3,X1] : (~r2_hidden(X3,k1_xboole_0) | ~r1_xboole_0(X1,X2)) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f67])).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    ( ! [X2,X3,X1] : (~r2_hidden(X3,k1_xboole_0) | ~r1_xboole_0(X1,X2) | ~r1_xboole_0(X1,X2)) )),
% 0.20/0.54    inference(superposition,[],[f43,f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.54  % (10466)Refutation not found, incomplete strategy% (10466)------------------------------
% 0.20/0.54  % (10466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10466)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10466)Memory used [KB]: 6268
% 0.20/0.54  % (10466)Time elapsed: 0.117 s
% 0.20/0.54  % (10466)------------------------------
% 0.20/0.54  % (10466)------------------------------
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    spl4_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f31,f59])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & r1_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1] : (X0 != X1 & r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.54    inference(negated_conjecture,[],[f14])).
% 0.20/0.54  fof(f14,conjecture,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ~spl4_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f32,f54])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    sK0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (10461)------------------------------
% 0.20/0.54  % (10461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10461)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (10461)Memory used [KB]: 6268
% 0.20/0.54  % (10461)Time elapsed: 0.097 s
% 0.20/0.54  % (10461)------------------------------
% 0.20/0.54  % (10461)------------------------------
% 0.20/0.54  % (10457)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.54  % (10458)Refutation not found, incomplete strategy% (10458)------------------------------
% 0.20/0.54  % (10458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10458)Memory used [KB]: 1791
% 0.20/0.54  % (10458)Time elapsed: 0.116 s
% 0.20/0.54  % (10458)------------------------------
% 0.20/0.54  % (10458)------------------------------
% 0.20/0.54  % (10463)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (10439)Success in time 0.185 s
%------------------------------------------------------------------------------
