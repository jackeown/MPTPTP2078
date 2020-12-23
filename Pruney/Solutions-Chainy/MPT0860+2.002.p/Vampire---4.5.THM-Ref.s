%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 (  56 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 ( 143 expanded)
%              Number of equality atoms :   29 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f58,f62])).

fof(f62,plain,
    ( spl5_1
    | spl5_3
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | spl5_1
    | spl5_3
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f34,f43,f34,f57,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X4
      | X1 = X4
      | X2 = X4
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f57,plain,
    ( r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl5_5
  <=> r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f43,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl5_3
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f34,plain,
    ( sK2 != k2_mcart_1(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl5_1
  <=> sK2 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f58,plain,
    ( spl5_5
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f52,f46,f55])).

fof(f46,plain,
    ( spl5_4
  <=> r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f52,plain,
    ( r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK3))
    | ~ spl5_4 ),
    inference(resolution,[],[f48,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f48,plain,
    ( r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK3)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f53,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f38,f48,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl5_2
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f49,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f46])).

fof(f23,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK3))) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f12,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f11,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ( k2_mcart_1(X0) != X3
          & k2_mcart_1(X0) != X2 )
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
       => ( ( k2_mcart_1(X0) = X3
            | k2_mcart_1(X0) = X2 )
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3)))
     => ( ( k2_mcart_1(X0) = X3
          | k2_mcart_1(X0) = X2 )
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).

fof(f44,plain,
    ( ~ spl5_3
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f10,f36,f41])).

fof(f10,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f9,f36,f32])).

fof(f9,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | sK2 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (12881)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.46  % (12865)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.46  % (12881)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f39,f44,f49,f53,f58,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl5_1 | spl5_3 | ~spl5_5),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    $false | (spl5_1 | spl5_3 | ~spl5_5)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f34,f43,f34,f57,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k1_enumset1(X0,X1,X2)) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 0.21/0.47    inference(equality_resolution,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (X0 = X4 | X1 = X4 | X2 = X4 | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK3)) | ~spl5_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    spl5_5 <=> r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    sK3 != k2_mcart_1(sK0) | spl5_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl5_3 <=> sK3 = k2_mcart_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    sK2 != k2_mcart_1(sK0) | spl5_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    spl5_1 <=> sK2 = k2_mcart_1(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl5_5 | ~spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f52,f46,f55])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    spl5_4 <=> r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK3)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK2,sK2,sK3)) | ~spl5_4),
% 0.21/0.47    inference(resolution,[],[f48,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK3))) | ~spl5_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f46])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl5_2 | ~spl5_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    $false | (spl5_2 | ~spl5_4)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f38,f48,f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ~r2_hidden(k1_mcart_1(sK0),sK1) | spl5_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    spl5_2 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl5_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f23,f46])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    r2_hidden(sK0,k2_zfmisc_1(sK1,k1_enumset1(sK2,sK2,sK3)))),
% 0.21/0.47    inference(definition_unfolding,[],[f11,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    r2_hidden(sK0,k2_zfmisc_1(sK1,k2_tarski(sK2,sK3)))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3] : (((k2_mcart_1(X0) != X3 & k2_mcart_1(X0) != X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(X1,k2_tarski(X2,X3))) => ((k2_mcart_1(X0) = X3 | k2_mcart_1(X0) = X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_mcart_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~spl5_3 | ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f10,f36,f41])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK3 != k2_mcart_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ~spl5_1 | ~spl5_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f9,f36,f32])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ~r2_hidden(k1_mcart_1(sK0),sK1) | sK2 != k2_mcart_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (12881)------------------------------
% 0.21/0.47  % (12881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12881)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (12881)Memory used [KB]: 10746
% 0.21/0.47  % (12881)Time elapsed: 0.071 s
% 0.21/0.47  % (12881)------------------------------
% 0.21/0.47  % (12881)------------------------------
% 0.21/0.47  % (12858)Success in time 0.109 s
%------------------------------------------------------------------------------
