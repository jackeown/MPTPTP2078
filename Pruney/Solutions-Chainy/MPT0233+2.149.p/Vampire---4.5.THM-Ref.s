%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  77 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 152 expanded)
%              Number of equality atoms :   25 (  54 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f67,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f63,f66])).

% (25347)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f66,plain,
    ( spl5_1
    | spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f64,f60,f31,f26])).

fof(f26,plain,
    ( spl5_1
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f31,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f60,plain,
    ( spl5_4
  <=> r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f64,plain,
    ( sK0 = sK2
    | sK0 = sK3
    | ~ spl5_4 ),
    inference(resolution,[],[f62,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_enumset1(X1,X1,X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f15,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f62,plain,
    ( r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f58,f36,f60])).

fof(f36,plain,
    ( spl5_3
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f58,plain,
    ( r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,
    ( r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl5_3 ),
    inference(resolution,[],[f53,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

% (25338)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f53,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_tarski(sK0),X0),k2_enumset1(sK2,sK2,sK2,sK3))
        | r1_tarski(k1_tarski(sK0),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f48,f38])).

fof(f38,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f48,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(k2_enumset1(X2,X2,X2,X5),X4)
      | r2_hidden(sK4(k1_tarski(X2),X3),X4)
      | r1_tarski(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f45,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(k1_tarski(X2),X3),k2_enumset1(X2,X2,X2,X4))
      | r1_tarski(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f14,f21])).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r2_hidden(sK4(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f16,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f11,f21,f21])).

fof(f11,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f34,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f12,f31])).

fof(f12,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f13,f26])).

fof(f13,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:47:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (25340)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (25335)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (25332)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (25340)Refutation not found, incomplete strategy% (25340)------------------------------
% 0.22/0.51  % (25340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25332)Refutation not found, incomplete strategy% (25332)------------------------------
% 0.22/0.51  % (25332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25332)Memory used [KB]: 1663
% 0.22/0.51  % (25332)Time elapsed: 0.098 s
% 0.22/0.51  % (25332)------------------------------
% 0.22/0.51  % (25332)------------------------------
% 0.22/0.51  % (25340)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (25340)Memory used [KB]: 10618
% 0.22/0.51  % (25340)Time elapsed: 0.095 s
% 0.22/0.51  % (25340)------------------------------
% 0.22/0.51  % (25340)------------------------------
% 0.22/0.52  % (25355)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (25342)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (25348)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (25348)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f29,f34,f39,f63,f66])).
% 0.22/0.52  % (25347)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl5_1 | spl5_2 | ~spl5_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f64,f60,f31,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    spl5_1 <=> sK0 = sK3),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    spl5_2 <=> sK0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    spl5_4 <=> r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    sK0 = sK2 | sK0 = sK3 | ~spl5_4),
% 0.22/0.52    inference(resolution,[],[f62,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f20,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f15,f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl5_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f60])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    spl5_4 | ~spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f58,f36,f60])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    spl5_3 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl5_3),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) | r1_tarski(k1_tarski(sK0),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl5_3),
% 0.22/0.52    inference(resolution,[],[f53,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.52  % (25338)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK4(k1_tarski(sK0),X0),k2_enumset1(sK2,sK2,sK2,sK3)) | r1_tarski(k1_tarski(sK0),X0)) ) | ~spl5_3),
% 0.22/0.52    inference(resolution,[],[f48,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) | ~spl5_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f36])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X4,X2,X5,X3] : (~r1_tarski(k2_enumset1(X2,X2,X2,X5),X4) | r2_hidden(sK4(k1_tarski(X2),X3),X4) | r1_tarski(k1_tarski(X2),X3)) )),
% 0.22/0.52    inference(resolution,[],[f45,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X4,X2,X3] : (r2_hidden(sK4(k1_tarski(X2),X3),k2_enumset1(X2,X2,X2,X4)) | r1_tarski(k1_tarski(X2),X3)) )),
% 0.22/0.52    inference(resolution,[],[f42,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f14,f21])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r2_hidden(sK4(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(resolution,[],[f16,f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f9])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl5_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f36])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 0.22/0.52    inference(definition_unfolding,[],[f11,f21,f21])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.52    inference(negated_conjecture,[],[f6])).
% 0.22/0.52  fof(f6,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ~spl5_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f12,f31])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    sK0 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ~spl5_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f13,f26])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    sK0 != sK3),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (25348)------------------------------
% 0.22/0.52  % (25348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25348)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (25348)Memory used [KB]: 10746
% 0.22/0.52  % (25348)Time elapsed: 0.104 s
% 0.22/0.52  % (25348)------------------------------
% 0.22/0.52  % (25348)------------------------------
% 0.22/0.52  % (25342)Refutation not found, incomplete strategy% (25342)------------------------------
% 0.22/0.52  % (25342)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25331)Success in time 0.156 s
%------------------------------------------------------------------------------
