%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  50 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   74 ( 112 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f170,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f80,f154])).

fof(f154,plain,
    ( spl6_4
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f146,f45,f40,f77])).

fof(f77,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f40,plain,
    ( spl6_2
  <=> r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f45,plain,
    ( spl6_3
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f146,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f82,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK0,X1)
        | r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),X1)) )
    | ~ spl6_3 ),
    inference(resolution,[],[f52,f32])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f18,f13])).

fof(f13,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f52,plain,
    ( ! [X1] :
        ( r2_hidden(sK0,k5_xboole_0(k2_zfmisc_1(sK1,sK2),X1))
        | r2_hidden(sK0,X1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f23,f47])).

fof(f47,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f80,plain,
    ( ~ spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f75,f35,f77])).

fof(f35,plain,
    ( spl6_1
  <=> r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f75,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))
    | spl6_1 ),
    inference(backward_demodulation,[],[f37,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f37,plain,
    ( ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f48,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f10,f45])).

fof(f10,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(f43,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f11,f40])).

fof(f11,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f12,f35])).

fof(f12,plain,(
    ~ r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:04:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (12238)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.50  % (12238)Refutation not found, incomplete strategy% (12238)------------------------------
% 0.22/0.50  % (12238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12231)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (12238)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12238)Memory used [KB]: 10618
% 0.22/0.51  % (12238)Time elapsed: 0.096 s
% 0.22/0.51  % (12238)------------------------------
% 0.22/0.51  % (12238)------------------------------
% 0.22/0.51  % (12241)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (12246)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (12246)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (12232)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f38,f43,f48,f80,f154])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    spl6_4 | ~spl6_2 | ~spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f45,f40,f77])).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    spl6_4 <=> r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    spl6_2 <=> r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl6_3 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) | (~spl6_2 | ~spl6_3)),
% 0.22/0.52    inference(resolution,[],[f82,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4)) | ~spl6_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f40])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X1] : (~r2_hidden(sK0,X1) | r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),X1))) ) | ~spl6_3),
% 0.22/0.52    inference(resolution,[],[f52,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f18,f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X1] : (r2_hidden(sK0,k5_xboole_0(k2_zfmisc_1(sK1,sK2),X1)) | r2_hidden(sK0,X1)) ) | ~spl6_3),
% 0.22/0.52    inference(resolution,[],[f23,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) | ~spl6_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f45])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ~spl6_4 | spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f75,f35,f77])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    spl6_1 <=> r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.52  fof(f75,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k3_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK3,sK4))) | spl6_1),
% 0.22/0.52    inference(backward_demodulation,[],[f37,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4))) | spl6_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f35])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    spl6_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f10,f45])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.52    inference(flattening,[],[f7])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & (r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.22/0.52    inference(negated_conjecture,[],[f5])).
% 0.22/0.52  fof(f5,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    spl6_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f11,f40])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    r2_hidden(sK0,k2_zfmisc_1(sK3,sK4))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~spl6_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f12,f35])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ~r2_hidden(sK0,k2_zfmisc_1(k3_xboole_0(sK1,sK3),k3_xboole_0(sK2,sK4)))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (12246)------------------------------
% 0.22/0.52  % (12246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12246)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (12246)Memory used [KB]: 10746
% 0.22/0.52  % (12246)Time elapsed: 0.105 s
% 0.22/0.52  % (12246)------------------------------
% 0.22/0.52  % (12246)------------------------------
% 0.22/0.52  % (12247)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.52  % (12229)Success in time 0.159 s
%------------------------------------------------------------------------------
