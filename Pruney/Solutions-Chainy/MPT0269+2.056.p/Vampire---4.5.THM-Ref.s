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
% DateTime   : Thu Dec  3 12:40:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  52 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  97 expanded)
%              Number of equality atoms :   33 (  71 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f43,f59])).

fof(f59,plain,(
    ~ spl2_1 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f34,f18,f19,f47])).

fof(f47,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,k2_tarski(X2,X2))
      | k2_tarski(X2,X2) = X3
      | ~ r2_hidden(X2,X3) ) ),
    inference(superposition,[],[f13,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f16,f12])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f9,f12])).

fof(f9,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f18,plain,(
    sK0 != k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f11,f12])).

fof(f11,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f43,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f41])).

fof(f41,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f10,f38])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f10,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f27,f36,f32])).

fof(f27,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f19,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f14,f12])).

% (24224)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (24216)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.48  % (24216)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f40,f43,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ~spl2_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    $false | ~spl2_1),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f34,f18,f19,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X3,k2_tarski(X2,X2)) | k2_tarski(X2,X2) = X3 | ~r2_hidden(X2,X3)) )),
% 0.20/0.48    inference(superposition,[],[f13,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f16,f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1))),
% 0.20/0.48    inference(definition_unfolding,[],[f9,f12])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    sK0 != k2_tarski(sK1,sK1)),
% 0.20/0.48    inference(definition_unfolding,[],[f11,f12])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    sK0 != k1_tarski(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    r2_hidden(sK1,sK0) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    spl2_1 <=> r2_hidden(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ~spl2_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    $false | ~spl2_2),
% 0.20/0.48    inference(subsumption_resolution,[],[f10,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    spl2_2 <=> k1_xboole_0 = sK0),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    k1_xboole_0 != sK0),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl2_1 | spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f27,f36,f32])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0)),
% 0.20/0.48    inference(superposition,[],[f19,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f14,f12])).
% 0.20/0.48  % (24224)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (24216)------------------------------
% 0.20/0.48  % (24216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24216)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (24216)Memory used [KB]: 6268
% 0.20/0.48  % (24216)Time elapsed: 0.078 s
% 0.20/0.48  % (24216)------------------------------
% 0.20/0.48  % (24216)------------------------------
% 0.20/0.48  % (24202)Success in time 0.126 s
%------------------------------------------------------------------------------
