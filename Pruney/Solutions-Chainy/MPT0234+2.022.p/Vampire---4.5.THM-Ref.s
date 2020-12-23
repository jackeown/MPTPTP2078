%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:27 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   16 (  19 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   22 (  28 expanded)
%              Number of equality atoms :   21 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(subsumption_resolution,[],[f24,f9])).

fof(f9,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f24,plain,(
    sK0 = sK1 ),
    inference(trivial_inequality_removal,[],[f22])).

fof(f22,plain,
    ( k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | sK0 = sK1 ),
    inference(superposition,[],[f19,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f19,plain,(
    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))) ),
    inference(definition_unfolding,[],[f10,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f10,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:02:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (1086)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.48  % (1096)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.49  % (1075)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (1097)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.49  % (1087)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (1096)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(subsumption_resolution,[],[f24,f9])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    sK0 != sK1),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,plain,(
% 0.19/0.50    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 0.19/0.50    inference(ennf_transformation,[],[f7])).
% 0.19/0.50  fof(f7,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.50    inference(negated_conjecture,[],[f6])).
% 0.19/0.50  fof(f6,conjecture,(
% 0.19/0.50    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    sK0 = sK1),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f22])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | sK0 = sK1),
% 0.19/0.50    inference(superposition,[],[f19,f15])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.19/0.50    inference(cnf_transformation,[],[f5])).
% 0.19/0.50  fof(f5,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),
% 0.19/0.50    inference(definition_unfolding,[],[f10,f17])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f13,f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.19/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (1096)------------------------------
% 0.19/0.50  % (1096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (1096)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (1096)Memory used [KB]: 1663
% 0.19/0.50  % (1096)Time elapsed: 0.101 s
% 0.19/0.50  % (1096)------------------------------
% 0.19/0.50  % (1096)------------------------------
% 0.19/0.50  % (1072)Success in time 0.146 s
%------------------------------------------------------------------------------
