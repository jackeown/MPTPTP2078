%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 104 expanded)
%              Number of leaves         :    6 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   78 ( 161 expanded)
%              Number of equality atoms :   43 ( 113 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(subsumption_resolution,[],[f112,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

fof(f20,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f112,plain,(
    ~ r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f111])).

fof(f111,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f50,f109])).

fof(f109,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f108,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f108,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f103])).

fof(f103,plain,
    ( sK0 != sK0
    | ~ r1_tarski(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f49,f101])).

fof(f101,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,
    ( r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))
    | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f18,f38,f38])).

fof(f18,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))
      | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f38,f38])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f40])).

fof(f40,plain,
    ( sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f17,f38,f38])).

fof(f17,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f41])).

fof(f41,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f16,f38])).

fof(f16,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:37:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (17139)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.48  % (17147)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.48  % (17139)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f112,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(k1_xboole_0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f28,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f20,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f35,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X0 | r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f111])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(backward_demodulation,[],[f50,f109])).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    k1_xboole_0 = sK0),
% 0.20/0.48    inference(subsumption_resolution,[],[f108,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.20/0.48    inference(resolution,[],[f26,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    sK0 != sK0 | ~r1_tarski(sK0,sK0) | k1_xboole_0 = sK0),
% 0.20/0.48    inference(superposition,[],[f49,f101])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f100])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.48    inference(resolution,[],[f44,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)) | sK0 = k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 0.20/0.48    inference(definition_unfolding,[],[f18,f38,f38])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k4_enumset1(X1,X1,X1,X1,X1,X1)) | k4_enumset1(X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f27,f38,f38])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,sK0)),
% 0.20/0.48    inference(inner_rewriting,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    sK0 != k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(definition_unfolding,[],[f17,f38,f38])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(inner_rewriting,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),
% 0.20/0.48    inference(definition_unfolding,[],[f16,f38])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (17139)------------------------------
% 0.20/0.48  % (17139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (17139)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (17139)Memory used [KB]: 6268
% 0.20/0.48  % (17139)Time elapsed: 0.071 s
% 0.20/0.48  % (17139)------------------------------
% 0.20/0.48  % (17139)------------------------------
% 0.20/0.48  % (17132)Success in time 0.127 s
%------------------------------------------------------------------------------
