%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  48 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   70 (  89 expanded)
%              Number of equality atoms :   16 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f74,f89])).

fof(f89,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f49,f73,f58])).

fof(f58,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k3_tarski(k1_enumset1(X2,X2,X3)),sK2)
        | ~ r2_hidden(sK0,X2) )
    | spl6_1 ),
    inference(resolution,[],[f56,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f12,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f56,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ r1_tarski(X0,sK2) )
    | spl6_1 ),
    inference(resolution,[],[f54,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f54,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl6_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f73,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl6_2
  <=> r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f49,plain,(
    ! [X3,X1] : r2_hidden(X3,k1_enumset1(X3,X3,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k1_enumset1(X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f27,f13])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f74,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f10,f29,f13])).

fof(f10,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f55,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f11,f52])).

fof(f11,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:09:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (21438)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.47  % (21438)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (21427)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f55,f74,f89])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl6_1 | ~spl6_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f83])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    $false | (spl6_1 | ~spl6_2)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f49,f73,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X2,X3] : (~r1_tarski(k3_tarski(k1_enumset1(X2,X2,X3)),sK2) | ~r2_hidden(sK0,X2)) ) | spl6_1),
% 0.21/0.47    inference(resolution,[],[f56,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X3,X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.21/0.47    inference(definition_unfolding,[],[f21,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f12,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_tarski(X0,sK2)) ) | spl6_1),
% 0.21/0.47    inference(resolution,[],[f54,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK2) | spl6_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    spl6_1 <=> r2_hidden(sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) | ~spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl6_2 <=> r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X3,X1] : (r2_hidden(X3,k1_enumset1(X3,X3,X1))) )),
% 0.21/0.47    inference(equality_resolution,[],[f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k1_enumset1(X3,X3,X1) != X2) )),
% 0.21/0.47    inference(equality_resolution,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 0.21/0.47    inference(definition_unfolding,[],[f27,f13])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl6_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f71])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)),
% 0.21/0.47    inference(definition_unfolding,[],[f10,f29,f13])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~spl6_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f11,f52])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (21438)------------------------------
% 0.21/0.47  % (21438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21438)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (21438)Memory used [KB]: 10746
% 0.21/0.47  % (21438)Time elapsed: 0.066 s
% 0.21/0.47  % (21438)------------------------------
% 0.21/0.47  % (21438)------------------------------
% 0.21/0.48  % (21411)Success in time 0.12 s
%------------------------------------------------------------------------------
