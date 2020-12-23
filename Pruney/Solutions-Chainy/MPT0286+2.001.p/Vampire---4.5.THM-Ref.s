%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   10 (  10 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    6
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f9])).

fof(f9,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(definition_unfolding,[],[f7,f8])).

fof(f8,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f7,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1] : k3_tarski(k2_tarski(X0,X1)) != k2_xboole_0(X0,X1)
   => k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] : k3_tarski(k2_tarski(X0,X1)) != k2_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:44:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (5541)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.46  % (5541)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    k3_tarski(k2_tarski(sK0,sK1)) != k3_tarski(k2_tarski(sK0,sK1))),
% 0.21/0.46    inference(definition_unfolding,[],[f7,f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1] : k3_tarski(k2_tarski(X0,X1)) != k2_xboole_0(X0,X1) => k3_tarski(k2_tarski(sK0,sK1)) != k2_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f4,plain,(
% 0.21/0.46    ? [X0,X1] : k3_tarski(k2_tarski(X0,X1)) != k2_xboole_0(X0,X1)),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    inference(negated_conjecture,[],[f2])).
% 0.21/0.46  fof(f2,conjecture,(
% 0.21/0.46    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (5541)------------------------------
% 0.21/0.46  % (5541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (5541)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (5541)Memory used [KB]: 10490
% 0.21/0.46  % (5541)Time elapsed: 0.005 s
% 0.21/0.46  % (5541)------------------------------
% 0.21/0.46  % (5541)------------------------------
% 0.21/0.47  % (5518)Success in time 0.1 s
%------------------------------------------------------------------------------
