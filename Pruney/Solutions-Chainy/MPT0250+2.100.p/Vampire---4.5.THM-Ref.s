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
% DateTime   : Thu Dec  3 12:38:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  52 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   76 ( 104 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f41,f59,f84,f102,f108])).

fof(f108,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f106,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f106,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_10 ),
    inference(resolution,[],[f101,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f101,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_10
  <=> r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f102,plain,
    ( ~ spl4_10
    | spl4_8 ),
    inference(avatar_split_clause,[],[f90,f81,f99])).

fof(f81,plain,
    ( spl4_8
  <=> sP3(sK0,sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f90,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_8 ),
    inference(resolution,[],[f83,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f83,plain,
    ( ~ sP3(sK0,sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f84,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f65,f56,f31,f81])).

fof(f31,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f56,plain,
    ( spl4_5
  <=> sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f65,plain,
    ( ~ sP3(sK0,sK1,k2_xboole_0(k1_tarski(sK0),sK1))
    | spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f60,f33])).

fof(f33,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f60,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ sP3(X0,sK1,k2_xboole_0(k1_tarski(sK0),sK1)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f29,f58])).

fof(f58,plain,
    ( sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f59,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f47,f38,f56])).

fof(f38,plain,
    ( spl4_2
  <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f47,plain,
    ( sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f40,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f40,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f12,f38])).

fof(f12,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f34,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f13,f31])).

fof(f13,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21994)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (22002)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.47  % (22002)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f34,f41,f59,f84,f102,f108])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl4_10),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    $false | spl4_10),
% 0.20/0.47    inference(subsumption_resolution,[],[f106,f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    ~r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),sK1)) | spl4_10),
% 0.20/0.47    inference(resolution,[],[f101,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),sK1)) | spl4_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f99])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    spl4_10 <=> r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    ~spl4_10 | spl4_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f90,f81,f99])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    spl4_8 <=> sP3(sK0,sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ~r2_hidden(sK0,k2_xboole_0(k1_tarski(sK0),sK1)) | spl4_8),
% 0.20/0.47    inference(resolution,[],[f83,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~sP3(sK0,sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f81])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ~spl4_8 | spl4_1 | ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f65,f56,f31,f81])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    spl4_5 <=> sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ~sP3(sK0,sK1,k2_xboole_0(k1_tarski(sK0),sK1)) | (spl4_1 | ~spl4_5)),
% 0.20/0.47    inference(resolution,[],[f60,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ~r2_hidden(sK0,sK1) | spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f31])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(X0,sK1) | ~sP3(X0,sK1,k2_xboole_0(k1_tarski(sK0),sK1))) ) | ~spl4_5),
% 0.20/0.47    inference(superposition,[],[f29,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f56])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~sP3(X3,X1,X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    spl4_5 | ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f38,f56])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    spl4_2 <=> r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl4_2),
% 0.20/0.47    inference(resolution,[],[f40,f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) | ~spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f38])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f12,f38])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f13,f31])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ~r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22002)------------------------------
% 0.20/0.47  % (22002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22002)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22002)Memory used [KB]: 10746
% 0.20/0.47  % (22002)Time elapsed: 0.086 s
% 0.20/0.47  % (22002)------------------------------
% 0.20/0.47  % (22002)------------------------------
% 0.20/0.48  % (21981)Success in time 0.122 s
%------------------------------------------------------------------------------
