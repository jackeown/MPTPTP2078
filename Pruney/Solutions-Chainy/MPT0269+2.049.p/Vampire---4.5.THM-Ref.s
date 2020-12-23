%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   52 (  95 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   89 ( 153 expanded)
%              Number of equality atoms :   43 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f62,f67,f70])).

fof(f70,plain,
    ( ~ spl2_4
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | ~ spl2_4
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f61,f66,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f23,f30])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f66,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl2_5
  <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f61,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl2_4
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f67,plain,
    ( ~ spl2_5
    | spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f57,f49,f44,f64])).

fof(f44,plain,
    ( spl2_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f49,plain,
    ( spl2_3
  <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f56,f17])).

fof(f17,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f56,plain,
    ( sK0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f33,f51])).

fof(f51,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,
    ( spl2_4
    | spl2_1
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f53,f49,f39,f59])).

fof(f39,plain,
    ( spl2_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f53,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f51,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f25,f21,f30])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f52,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f14,f21,f30])).

fof(f14,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f47,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f31,f44])).

fof(f31,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f16,f30])).

fof(f16,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.48  % (17332)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.49  % (17334)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.49  % (17332)Refutation not found, incomplete strategy% (17332)------------------------------
% 0.22/0.49  % (17332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17332)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (17332)Memory used [KB]: 10618
% 0.22/0.49  % (17332)Time elapsed: 0.072 s
% 0.22/0.49  % (17332)------------------------------
% 0.22/0.49  % (17332)------------------------------
% 0.22/0.49  % (17334)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f42,f47,f52,f62,f67,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ~spl2_4 | spl2_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f68])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    $false | (~spl2_4 | spl2_5)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f61,f66,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f23,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f18,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f19,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | spl2_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    spl2_5 <=> r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    r2_hidden(sK1,sK0) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl2_4 <=> r2_hidden(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ~spl2_5 | spl2_2 | ~spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f57,f49,f44,f64])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl2_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl2_3 <=> k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_3),
% 0.22/0.49    inference(forward_demodulation,[],[f56,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    sK0 = k5_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) | ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | ~spl2_3),
% 0.22/0.49    inference(superposition,[],[f33,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f22,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f20,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_4 | spl2_1 | ~spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f53,f49,f39,f59])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    spl2_1 <=> k1_xboole_0 = sK0),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0) | ~spl2_3),
% 0.22/0.49    inference(superposition,[],[f51,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 0.22/0.49    inference(definition_unfolding,[],[f25,f21,f30])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f49])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.22/0.49    inference(definition_unfolding,[],[f14,f21,f30])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f44])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.22/0.49    inference(definition_unfolding,[],[f16,f30])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    sK0 != k1_tarski(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f39])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    k1_xboole_0 != sK0),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (17334)------------------------------
% 0.22/0.49  % (17334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (17334)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (17334)Memory used [KB]: 10618
% 0.22/0.49  % (17334)Time elapsed: 0.086 s
% 0.22/0.49  % (17334)------------------------------
% 0.22/0.49  % (17334)------------------------------
% 0.22/0.50  % (17310)Success in time 0.136 s
%------------------------------------------------------------------------------
