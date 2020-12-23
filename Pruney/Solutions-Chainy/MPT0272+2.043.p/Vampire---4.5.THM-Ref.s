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
% DateTime   : Thu Dec  3 12:41:17 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   24 (  39 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  67 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f15,f13])).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f19,plain,(
    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f11,f13])).

fof(f11,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f43,plain,(
    r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f38])).

fof(f38,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f18,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f13,f13])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f18,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f12,f13,f13])).

fof(f12,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:36:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.18/0.43  % (27060)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.44  % (27066)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.18/0.44  % (27059)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.18/0.44  % (27060)Refutation found. Thanks to Tanya!
% 0.18/0.44  % SZS status Theorem for theBenchmark
% 0.18/0.44  % SZS output start Proof for theBenchmark
% 0.18/0.44  fof(f44,plain,(
% 0.18/0.44    $false),
% 0.18/0.44    inference(resolution,[],[f43,f26])).
% 0.18/0.44  fof(f26,plain,(
% 0.18/0.44    ~r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(trivial_inequality_removal,[],[f25])).
% 0.18/0.44  fof(f25,plain,(
% 0.18/0.44    k1_xboole_0 != k1_xboole_0 | ~r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(superposition,[],[f19,f20])).
% 0.18/0.44  fof(f20,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(definition_unfolding,[],[f15,f13])).
% 0.18/0.44  fof(f13,plain,(
% 0.18/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f1])).
% 0.18/0.44  fof(f1,axiom,(
% 0.18/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.44  fof(f15,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f9])).
% 0.18/0.44  fof(f9,plain,(
% 0.18/0.44    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0))),
% 0.18/0.44    inference(nnf_transformation,[],[f3])).
% 0.18/0.44  fof(f3,axiom,(
% 0.18/0.44    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 <=> r2_hidden(X0,X1))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).
% 0.18/0.44  fof(f19,plain,(
% 0.18/0.44    k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 0.18/0.44    inference(definition_unfolding,[],[f11,f13])).
% 0.18/0.44  fof(f11,plain,(
% 0.18/0.44    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f8])).
% 0.18/0.44  fof(f8,plain,(
% 0.18/0.44    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).
% 0.18/0.44  fof(f7,plain,(
% 0.18/0.44    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.18/0.44    introduced(choice_axiom,[])).
% 0.18/0.44  fof(f6,plain,(
% 0.18/0.44    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0)),
% 0.18/0.44    inference(ennf_transformation,[],[f5])).
% 0.18/0.44  fof(f5,negated_conjecture,(
% 0.18/0.44    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 0.18/0.44    inference(negated_conjecture,[],[f4])).
% 0.18/0.44  fof(f4,conjecture,(
% 0.18/0.44    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.18/0.44  fof(f43,plain,(
% 0.18/0.44    r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(trivial_inequality_removal,[],[f38])).
% 0.18/0.44  fof(f38,plain,(
% 0.18/0.44    k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) | r2_hidden(sK0,sK1)),
% 0.18/0.44    inference(superposition,[],[f18,f22])).
% 0.18/0.44  fof(f22,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(definition_unfolding,[],[f17,f13,f13])).
% 0.18/0.44  fof(f17,plain,(
% 0.18/0.44    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.18/0.44    inference(cnf_transformation,[],[f10])).
% 0.18/0.44  fof(f10,plain,(
% 0.18/0.44    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.18/0.44    inference(nnf_transformation,[],[f2])).
% 0.18/0.44  fof(f2,axiom,(
% 0.18/0.44    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 0.18/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 0.18/0.44  fof(f18,plain,(
% 0.18/0.44    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK1)),
% 0.18/0.44    inference(definition_unfolding,[],[f12,f13,f13])).
% 0.18/0.44  fof(f12,plain,(
% 0.18/0.44    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.18/0.44    inference(cnf_transformation,[],[f8])).
% 0.18/0.44  % SZS output end Proof for theBenchmark
% 0.18/0.44  % (27060)------------------------------
% 0.18/0.44  % (27060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (27060)Termination reason: Refutation
% 0.18/0.44  
% 0.18/0.44  % (27060)Memory used [KB]: 6012
% 0.18/0.44  % (27060)Time elapsed: 0.054 s
% 0.18/0.44  % (27060)------------------------------
% 0.18/0.44  % (27060)------------------------------
% 0.18/0.44  % (27055)Success in time 0.11 s
%------------------------------------------------------------------------------
