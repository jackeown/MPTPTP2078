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
% DateTime   : Thu Dec  3 12:58:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  70 expanded)
%              Number of leaves         :    8 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   60 ( 115 expanded)
%              Number of equality atoms :   21 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f50,f59])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f43,f51,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f20,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f51,plain,
    ( k1_enumset1(sK1,sK1,sK1) = k4_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0)))
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f16,f20,f20,f20])).

fof(f16,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f34,plain,
    ( sK1 != k1_mcart_1(sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> sK1 = k1_mcart_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,(
    r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f21,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f21,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2)) ),
    inference(definition_unfolding,[],[f11,f20])).

fof(f11,plain,(
    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | k1_mcart_1(X0) != X1 )
      & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & k1_mcart_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & k1_mcart_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

fof(f50,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f30,f21,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_1
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f10,f32,f28])).

fof(f10,plain,
    ( sK1 != k1_mcart_1(sK0)
    | ~ r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:00:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (3539)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (3539)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f35,f50,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    $false | spl3_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f43,f51,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k1_enumset1(X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f15,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f18,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    k1_enumset1(sK1,sK1,sK1) = k4_xboole_0(k1_enumset1(sK1,sK1,sK1),k1_enumset1(k1_mcart_1(sK0),k1_mcart_1(sK0),k1_mcart_1(sK0))) | spl3_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f34,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.21/0.50    inference(definition_unfolding,[],[f16,f20,f20,f20])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X0,X1] : (X0 = X1 | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    sK1 != k1_mcart_1(sK0) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    spl3_2 <=> sK1 = k1_mcart_1(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    r2_hidden(k1_mcart_1(sK0),k1_enumset1(sK1,sK1,sK1))),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f21,f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_zfmisc_1(k1_enumset1(sK1,sK1,sK1),sK2))),
% 0.21/0.50    inference(definition_unfolding,[],[f11,f20])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    r2_hidden(sK0,k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | k1_mcart_1(X0) != X1) & r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(k1_tarski(X1),X2)) => (r2_hidden(k2_mcart_1(X0),X2) & k1_mcart_1(X0) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    $false | spl3_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f30,f21,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~r2_hidden(k2_mcart_1(sK0),sK2) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    spl3_1 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~spl3_1 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f10,f32,f28])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    sK1 != k1_mcart_1(sK0) | ~r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3539)------------------------------
% 0.21/0.50  % (3539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3539)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3539)Memory used [KB]: 6268
% 0.21/0.50  % (3539)Time elapsed: 0.096 s
% 0.21/0.50  % (3539)------------------------------
% 0.21/0.50  % (3539)------------------------------
% 0.21/0.50  % (3532)Success in time 0.142 s
%------------------------------------------------------------------------------
