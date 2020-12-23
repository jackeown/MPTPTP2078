%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   12 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :  104 ( 145 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f48,f53,f101,f114,f120])).

fof(f120,plain,
    ( spl7_1
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl7_1
    | ~ spl7_6
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f52,f31,f52,f52,f113])).

fof(f113,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0),X0)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k9_relat_1(X0,X1) = X2
        | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_18
  <=> ! [X1,X0,X2] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k9_relat_1(X0,X1) = X2
        | r2_hidden(sK4(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f31,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl7_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f52,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_6
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f114,plain,
    ( spl7_18
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f106,f99,f46,f112])).

fof(f46,plain,
    ( spl7_5
  <=> ! [X0] :
        ( r2_hidden(sK4(X0),X0)
        | v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f99,plain,
    ( spl7_16
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k9_relat_1(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k9_relat_1(X0,X1) = X2
        | r2_hidden(sK4(X0),X0) )
    | ~ spl7_5
    | ~ spl7_16 ),
    inference(resolution,[],[f100,f47])).

fof(f47,plain,
    ( ! [X0] :
        ( v1_relat_1(X0)
        | r2_hidden(sK4(X0),X0) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f100,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0)
        | r2_hidden(sK1(X0,X1,X2),X2)
        | k9_relat_1(X0,X1) = X2 )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f99])).

fof(f101,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f12,f99])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f53,plain,
    ( spl7_6
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f49,f38,f34,f51])).

fof(f34,plain,
    ( spl7_2
  <=> ! [X1,X0] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f38,plain,
    ( spl7_3
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f49,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(superposition,[],[f35,f39])).

fof(f39,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f35,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f48,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f18,f46])).

fof(f18,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f40,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f38])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f36,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f32,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f10,f30])).

fof(f10,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (8040)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (8048)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (8043)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (8048)Refutation not found, incomplete strategy% (8048)------------------------------
% 0.22/0.49  % (8048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8048)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (8048)Memory used [KB]: 1535
% 0.22/0.49  % (8048)Time elapsed: 0.070 s
% 0.22/0.49  % (8048)------------------------------
% 0.22/0.49  % (8048)------------------------------
% 0.22/0.50  % (8038)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (8038)Refutation not found, incomplete strategy% (8038)------------------------------
% 0.22/0.50  % (8038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8038)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (8038)Memory used [KB]: 10490
% 0.22/0.50  % (8038)Time elapsed: 0.081 s
% 0.22/0.50  % (8038)------------------------------
% 0.22/0.50  % (8038)------------------------------
% 0.22/0.51  % (8044)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (8041)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (8047)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (8047)Refutation not found, incomplete strategy% (8047)------------------------------
% 0.22/0.51  % (8047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (8047)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (8047)Memory used [KB]: 6012
% 0.22/0.51  % (8047)Time elapsed: 0.002 s
% 0.22/0.51  % (8047)------------------------------
% 0.22/0.51  % (8047)------------------------------
% 0.22/0.51  % (8035)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (8050)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.52  % (8035)Refutation not found, incomplete strategy% (8035)------------------------------
% 0.22/0.52  % (8035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8035)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8035)Memory used [KB]: 6140
% 0.22/0.52  % (8035)Time elapsed: 0.095 s
% 0.22/0.52  % (8035)------------------------------
% 0.22/0.52  % (8035)------------------------------
% 0.22/0.52  % (8042)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.52  % (8055)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (8055)Refutation not found, incomplete strategy% (8055)------------------------------
% 0.22/0.52  % (8055)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8055)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8055)Memory used [KB]: 10490
% 0.22/0.52  % (8055)Time elapsed: 0.090 s
% 0.22/0.52  % (8055)------------------------------
% 0.22/0.52  % (8055)------------------------------
% 0.22/0.52  % (8046)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.52  % (8039)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (8044)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f32,f36,f40,f48,f53,f101,f114,f120])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl7_1 | ~spl7_6 | ~spl7_18),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    $false | (spl7_1 | ~spl7_6 | ~spl7_18)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f52,f31,f52,f52,f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0)) ) | ~spl7_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f112])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl7_18 <=> ! [X1,X0,X2] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0),X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl7_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    spl7_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl7_6 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl7_18 | ~spl7_5 | ~spl7_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f106,f99,f46,f112])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    spl7_5 <=> ! [X0] : (r2_hidden(sK4(X0),X0) | v1_relat_1(X0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    spl7_16 <=> ! [X1,X0,X2] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0),X0)) ) | (~spl7_5 | ~spl7_16)),
% 0.22/0.53    inference(resolution,[],[f100,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK4(X0),X0)) ) | ~spl7_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f46])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2) ) | ~spl7_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f99])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    spl7_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f12,f99])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK1(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k9_relat_1(X0,X1) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    spl7_6 | ~spl7_2 | ~spl7_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f49,f38,f34,f51])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    spl7_2 <=> ! [X1,X0] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    spl7_3 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl7_2 | ~spl7_3)),
% 0.22/0.53    inference(superposition,[],[f35,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl7_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f38])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) ) | ~spl7_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f34])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    spl7_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f18,f46])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    spl7_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f27,f38])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    spl7_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f34])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ~spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f10,f30])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (8044)------------------------------
% 0.22/0.53  % (8044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8044)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (8044)Memory used [KB]: 10618
% 0.22/0.53  % (8044)Time elapsed: 0.068 s
% 0.22/0.53  % (8044)------------------------------
% 0.22/0.53  % (8044)------------------------------
% 0.22/0.53  % (8054)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.53  % (8049)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (8034)Success in time 0.171 s
%------------------------------------------------------------------------------
