%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 146 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 261 expanded)
%              Number of equality atoms :   49 ( 154 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f55,f80,f253])).

fof(f253,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f89,f240,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f25])).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f240,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK2))
    | spl4_2
    | spl4_3 ),
    inference(superposition,[],[f34,f96])).

fof(f96,plain,
    ( k1_enumset1(sK1,sK1,sK2) = k4_xboole_0(k1_enumset1(k1_mcart_1(sK0),sK1,sK2),k1_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f43,f54,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)) = k1_enumset1(X1,X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f22,f26,f25])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | X0 = X2
      | k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)
      | X0 = X2
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2)
        & X0 != X2
        & X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

fof(f54,plain,
    ( sK2 != k1_mcart_1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_3
  <=> sK2 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f43,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl4_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f34,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) ) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f89,plain,
    ( r2_hidden(k1_mcart_1(sK0),k4_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK1,sK1,sK1)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f56,f43,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f26])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f27,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f27,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f15,f25,f26])).

fof(f15,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) != X3
        | ( k1_mcart_1(X0) != X2
          & k1_mcart_1(X0) != X1 ) )
      & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
       => ( k2_mcart_1(X0) = X3
          & ( k1_mcart_1(X0) = X2
            | k1_mcart_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3)))
     => ( k2_mcart_1(X0) = X3
        & ( k1_mcart_1(X0) = X2
          | k1_mcart_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

fof(f80,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f60,f67,f30])).

fof(f67,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK3,sK3,sK3))
    | spl4_1 ),
    inference(superposition,[],[f34,f45])).

fof(f45,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k4_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f23,f26,f26,f26])).

% (10074)Refutation not found, incomplete strategy% (10074)------------------------------
% (10074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10074)Termination reason: Refutation not found, incomplete strategy

% (10074)Memory used [KB]: 1663
% (10074)Time elapsed: 0.096 s
% (10074)------------------------------
% (10074)------------------------------
fof(f23,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f39,plain,
    ( sK3 != k2_mcart_1(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl4_1
  <=> sK3 = k2_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f60,plain,
    ( r2_hidden(k2_mcart_1(sK0),k4_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_enumset1(sK3,sK3,sK3)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f39,f57,f28])).

fof(f57,plain,(
    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK3,sK3,sK3)) ),
    inference(unit_resulting_resolution,[],[f27,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,
    ( ~ spl4_1
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f14,f52,f37])).

fof(f14,plain,
    ( sK2 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f44,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f41,f37])).

fof(f13,plain,
    ( sK1 != k1_mcart_1(sK0)
    | sK3 != k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (10057)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (10057)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (10074)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f44,f55,f80,f253])).
% 0.21/0.48  fof(f253,plain,(
% 0.21/0.48    spl4_2 | spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f246])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    $false | (spl4_2 | spl4_3)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f89,f240,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f19,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.48  fof(f240,plain,(
% 0.21/0.48    ~r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK2)) | (spl4_2 | spl4_3)),
% 0.21/0.48    inference(superposition,[],[f34,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_enumset1(sK1,sK1,sK2) = k4_xboole_0(k1_enumset1(k1_mcart_1(sK0),sK1,sK2),k1_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | (spl4_2 | spl4_3)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f43,f54,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)) = k1_enumset1(X1,X1,X2) | X0 = X2 | X0 = X1) )),
% 0.21/0.48    inference(definition_unfolding,[],[f22,f26,f25])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (X0 = X1 | X0 = X2 | k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) = k2_tarski(X1,X2) | X0 = X2 | X0 = X1)),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ~(k4_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X0)) != k2_tarski(X1,X2) & X0 != X2 & X0 != X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    sK2 != k1_mcart_1(sK0) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl4_3 <=> sK2 = k1_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    sK1 != k1_mcart_1(sK0) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl4_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f20,f26])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r2_hidden(k1_mcart_1(sK0),k4_xboole_0(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK1,sK1,sK1))) | spl4_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f56,f43,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_enumset1(X2,X2,X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(definition_unfolding,[],[f21,f26])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK2))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_zfmisc_1(k1_enumset1(sK1,sK1,sK2),k1_enumset1(sK3,sK3,sK3)))),
% 0.21/0.48    inference(definition_unfolding,[],[f15,f25,f26])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r2_hidden(sK0,k2_zfmisc_1(k2_tarski(sK1,sK2),k1_tarski(sK3)))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((k2_mcart_1(X0) != X3 | (k1_mcart_1(X0) != X2 & k1_mcart_1(X0) != X1)) & r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_hidden(X0,k2_zfmisc_1(k2_tarski(X1,X2),k1_tarski(X3))) => (k2_mcart_1(X0) = X3 & (k1_mcart_1(X0) = X2 | k1_mcart_1(X0) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f73])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    $false | spl4_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f60,f67,f30])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK3,sK3,sK3)) | spl4_1),
% 0.21/0.48    inference(superposition,[],[f34,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_enumset1(sK3,sK3,sK3) = k4_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_enumset1(k2_mcart_1(sK0),k2_mcart_1(sK0),k2_mcart_1(sK0))) | spl4_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f39,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f26,f26,f26])).
% 0.21/0.48  % (10074)Refutation not found, incomplete strategy% (10074)------------------------------
% 0.21/0.48  % (10074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10074)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10074)Memory used [KB]: 1663
% 0.21/0.48  % (10074)Time elapsed: 0.096 s
% 0.21/0.48  % (10074)------------------------------
% 0.21/0.48  % (10074)------------------------------
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    sK3 != k2_mcart_1(sK0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl4_1 <=> sK3 = k2_mcart_1(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    r2_hidden(k2_mcart_1(sK0),k4_xboole_0(k1_enumset1(sK3,sK3,sK3),k1_enumset1(sK3,sK3,sK3))) | spl4_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f39,f57,f28])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    r2_hidden(k2_mcart_1(sK0),k1_enumset1(sK3,sK3,sK3))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f27,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f52,f37])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    sK2 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f13,f41,f37])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    sK1 != k1_mcart_1(sK0) | sK3 != k2_mcart_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (10057)------------------------------
% 0.21/0.48  % (10057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10057)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (10057)Memory used [KB]: 6396
% 0.21/0.48  % (10057)Time elapsed: 0.083 s
% 0.21/0.48  % (10057)------------------------------
% 0.21/0.48  % (10057)------------------------------
% 0.21/0.48  % (10052)Success in time 0.123 s
%------------------------------------------------------------------------------
