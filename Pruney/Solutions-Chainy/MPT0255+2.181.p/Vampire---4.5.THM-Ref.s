%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  36 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  68 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f42,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f41])).

fof(f41,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f40])).

fof(f40,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f39,f35])).

fof(f35,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl3_1 ),
    inference(unit_resulting_resolution,[],[f33,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f33,plain,
    ( ! [X0] : r1_xboole_0(X0,sK2)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f32,f17])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f32,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | r1_xboole_0(X0,sK2) )
    | ~ spl3_1 ),
    inference(superposition,[],[f22,f28])).

fof(f28,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f39,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f38,f16])).

fof(f16,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f38,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | r2_hidden(sK0,sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f23,f28])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (29120)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.43  % (29120)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f29,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    $false | ~spl3_1),
% 0.20/0.43    inference(subsumption_resolution,[],[f39,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl3_1),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f33,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f19,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (r1_xboole_0(X0,sK2)) ) | ~spl3_1),
% 0.20/0.43    inference(subsumption_resolution,[],[f32,f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | r1_xboole_0(X0,sK2)) ) | ~spl3_1),
% 0.20/0.43    inference(superposition,[],[f22,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    spl3_1 <=> k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    r2_hidden(sK0,sK2) | ~spl3_1),
% 0.20/0.43    inference(subsumption_resolution,[],[f38,f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ~r1_tarski(k1_xboole_0,sK2) | r2_hidden(sK0,sK2) | ~spl3_1),
% 0.20/0.43    inference(superposition,[],[f23,f28])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) | r2_hidden(X0,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f26])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (29120)------------------------------
% 0.20/0.43  % (29120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (29120)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (29120)Memory used [KB]: 10618
% 0.20/0.43  % (29120)Time elapsed: 0.006 s
% 0.20/0.43  % (29120)------------------------------
% 0.20/0.43  % (29120)------------------------------
% 0.20/0.44  % (29104)Success in time 0.081 s
%------------------------------------------------------------------------------
