%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 (  83 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 194 expanded)
%              Number of equality atoms :   34 (  41 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f96,f223,f232,f241,f263,f308,f309])).

fof(f309,plain,
    ( k1_xboole_0 != sK1(k1_setfam_1(sK0))
    | r2_hidden(k1_xboole_0,sK1(k1_setfam_1(sK0)))
    | ~ r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f308,plain,
    ( spl7_22
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f302,f238,f305])).

fof(f305,plain,
    ( spl7_22
  <=> k1_xboole_0 = sK1(k1_setfam_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f238,plain,
    ( spl7_18
  <=> r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f302,plain,
    ( k1_xboole_0 = sK1(k1_setfam_1(sK0))
    | ~ spl7_18 ),
    inference(resolution,[],[f246,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f246,plain,
    ( ! [X0] : r2_hidden(sK1(k1_setfam_1(sK0)),X0)
    | ~ spl7_18 ),
    inference(resolution,[],[f240,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f57,f105])).

fof(f105,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f36,f100])).

fof(f100,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f32,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f240,plain,
    ( r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f238])).

fof(f263,plain,
    ( ~ spl7_21
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f252,f238,f260])).

fof(f260,plain,
    ( spl7_21
  <=> r2_hidden(k1_xboole_0,sK1(k1_setfam_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f252,plain,
    ( ~ r2_hidden(k1_xboole_0,sK1(k1_setfam_1(sK0)))
    | ~ spl7_18 ),
    inference(resolution,[],[f240,f29])).

fof(f241,plain,
    ( spl7_1
    | spl7_18
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f234,f217,f238,f59])).

fof(f59,plain,
    ( spl7_1
  <=> k1_xboole_0 = k1_setfam_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f217,plain,
    ( spl7_14
  <=> ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k1_setfam_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f234,plain,
    ( r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0)
    | k1_xboole_0 = k1_setfam_1(sK0)
    | ~ spl7_14 ),
    inference(resolution,[],[f218,f20])).

fof(f218,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_setfam_1(sK0))
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f217])).

fof(f232,plain,
    ( k1_xboole_0 != sK0
    | r2_hidden(sK0,k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f223,plain,
    ( spl7_14
    | spl7_15
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f209,f64,f220,f217])).

fof(f220,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f64,plain,
    ( spl7_2
  <=> r2_hidden(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f209,plain,
    ( ! [X2] :
        ( k1_xboole_0 = sK0
        | r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k1_setfam_1(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f52,f66])).

fof(f66,plain,
    ( r2_hidden(k1_xboole_0,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f52,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_setfam_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f96,plain,
    ( ~ spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f91,f64,f93])).

fof(f93,plain,
    ( spl7_7
  <=> r2_hidden(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f91,plain,
    ( ~ r2_hidden(sK0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(resolution,[],[f29,f66])).

fof(f67,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f17,f64])).

fof(f17,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_setfam_1(X0)
      & r2_hidden(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k1_setfam_1(X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,X0)
     => k1_xboole_0 = k1_setfam_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).

fof(f62,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f18,f59])).

fof(f18,plain,(
    k1_xboole_0 != k1_setfam_1(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (31663)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (31666)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (31661)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (31662)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (31657)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (31686)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (31680)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (31659)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (31671)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (31679)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (31681)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (31672)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (31667)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (31687)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (31684)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (31669)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (31658)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (31680)Refutation not found, incomplete strategy% (31680)------------------------------
% 0.20/0.52  % (31680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (31680)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (31680)Memory used [KB]: 10746
% 0.20/0.52  % (31680)Time elapsed: 0.106 s
% 0.20/0.52  % (31680)------------------------------
% 0.20/0.52  % (31680)------------------------------
% 0.20/0.52  % (31682)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (31675)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (31670)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (31660)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (31676)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (31664)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (31674)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (31685)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (31665)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (31677)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (31683)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (31675)Refutation not found, incomplete strategy% (31675)------------------------------
% 0.20/0.55  % (31675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31675)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31675)Memory used [KB]: 10618
% 0.20/0.55  % (31675)Time elapsed: 0.145 s
% 0.20/0.55  % (31675)------------------------------
% 0.20/0.55  % (31675)------------------------------
% 0.20/0.55  % (31668)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (31678)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (31674)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f310,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f62,f67,f96,f223,f232,f241,f263,f308,f309])).
% 0.20/0.56  fof(f309,plain,(
% 0.20/0.56    k1_xboole_0 != sK1(k1_setfam_1(sK0)) | r2_hidden(k1_xboole_0,sK1(k1_setfam_1(sK0))) | ~r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0)),
% 0.20/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.56  fof(f308,plain,(
% 0.20/0.56    spl7_22 | ~spl7_18),
% 0.20/0.56    inference(avatar_split_clause,[],[f302,f238,f305])).
% 0.20/0.56  fof(f305,plain,(
% 0.20/0.56    spl7_22 <=> k1_xboole_0 = sK1(k1_setfam_1(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    spl7_18 <=> r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.56  fof(f302,plain,(
% 0.20/0.56    k1_xboole_0 = sK1(k1_setfam_1(sK0)) | ~spl7_18),
% 0.20/0.56    inference(resolution,[],[f246,f97])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(X0,sK1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(resolution,[],[f20,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.56  fof(f246,plain,(
% 0.20/0.56    ( ! [X0] : (r2_hidden(sK1(k1_setfam_1(sK0)),X0)) ) | ~spl7_18),
% 0.20/0.56    inference(resolution,[],[f240,f131])).
% 0.20/0.56  fof(f131,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(X1,X0)) )),
% 0.20/0.56    inference(superposition,[],[f57,f105])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.20/0.56    inference(resolution,[],[f36,f100])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f99])).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.56    inference(resolution,[],[f32,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f16])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.20/0.56  fof(f240,plain,(
% 0.20/0.56    r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0) | ~spl7_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f238])).
% 0.20/0.56  fof(f263,plain,(
% 0.20/0.56    ~spl7_21 | ~spl7_18),
% 0.20/0.56    inference(avatar_split_clause,[],[f252,f238,f260])).
% 0.20/0.56  fof(f260,plain,(
% 0.20/0.56    spl7_21 <=> r2_hidden(k1_xboole_0,sK1(k1_setfam_1(sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.56  fof(f252,plain,(
% 0.20/0.56    ~r2_hidden(k1_xboole_0,sK1(k1_setfam_1(sK0))) | ~spl7_18),
% 0.20/0.56    inference(resolution,[],[f240,f29])).
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    spl7_1 | spl7_18 | ~spl7_14),
% 0.20/0.56    inference(avatar_split_clause,[],[f234,f217,f238,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    spl7_1 <=> k1_xboole_0 = k1_setfam_1(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.56  fof(f217,plain,(
% 0.20/0.56    spl7_14 <=> ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_setfam_1(sK0)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.56  fof(f234,plain,(
% 0.20/0.56    r2_hidden(sK1(k1_setfam_1(sK0)),k1_xboole_0) | k1_xboole_0 = k1_setfam_1(sK0) | ~spl7_14),
% 0.20/0.56    inference(resolution,[],[f218,f20])).
% 0.20/0.56  fof(f218,plain,(
% 0.20/0.56    ( ! [X2] : (~r2_hidden(X2,k1_setfam_1(sK0)) | r2_hidden(X2,k1_xboole_0)) ) | ~spl7_14),
% 0.20/0.56    inference(avatar_component_clause,[],[f217])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    k1_xboole_0 != sK0 | r2_hidden(sK0,k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.56    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.56  fof(f223,plain,(
% 0.20/0.56    spl7_14 | spl7_15 | ~spl7_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f209,f64,f220,f217])).
% 0.20/0.56  fof(f220,plain,(
% 0.20/0.56    spl7_15 <=> k1_xboole_0 = sK0),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    spl7_2 <=> r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.56  fof(f209,plain,(
% 0.20/0.56    ( ! [X2] : (k1_xboole_0 = sK0 | r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_setfam_1(sK0))) ) | ~spl7_2),
% 0.20/0.56    inference(resolution,[],[f52,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    r2_hidden(k1_xboole_0,sK0) | ~spl7_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f64])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k1_xboole_0 = X0 | r2_hidden(X2,X3) | ~r2_hidden(X2,k1_setfam_1(X0))) )),
% 0.20/0.56    inference(equality_resolution,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    ~spl7_7 | ~spl7_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f91,f64,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    spl7_7 <=> r2_hidden(sK0,k1_xboole_0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k1_xboole_0) | ~spl7_2),
% 0.20/0.56    inference(resolution,[],[f29,f66])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    spl7_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f17,f64])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    r2_hidden(k1_xboole_0,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ? [X0] : (k1_xboole_0 != k1_setfam_1(X0) & r2_hidden(k1_xboole_0,X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,negated_conjecture,(
% 0.20/0.56    ~! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.20/0.56    inference(negated_conjecture,[],[f10])).
% 0.20/0.56  fof(f10,conjecture,(
% 0.20/0.56    ! [X0] : (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k1_setfam_1(X0))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_setfam_1)).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ~spl7_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f18,f59])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    k1_xboole_0 != k1_setfam_1(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (31674)------------------------------
% 0.20/0.56  % (31674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (31674)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (31674)Memory used [KB]: 10874
% 0.20/0.56  % (31674)Time elapsed: 0.135 s
% 0.20/0.56  % (31674)------------------------------
% 0.20/0.56  % (31674)------------------------------
% 0.20/0.56  % (31654)Success in time 0.198 s
%------------------------------------------------------------------------------
