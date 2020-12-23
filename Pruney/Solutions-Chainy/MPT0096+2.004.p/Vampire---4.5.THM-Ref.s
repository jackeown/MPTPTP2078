%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   12 (  12 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,plain,(
    $false ),
    inference(resolution,[],[f11,f9])).

fof(f9,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f11,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f8,f10])).

fof(f10,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f8,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (30822)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (30822)Refutation not found, incomplete strategy% (30822)------------------------------
% 0.20/0.41  % (30822)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (30822)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (30822)Memory used [KB]: 10490
% 0.20/0.41  % (30822)Time elapsed: 0.003 s
% 0.20/0.41  % (30822)------------------------------
% 0.20/0.41  % (30822)------------------------------
% 0.20/0.44  % (30825)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.44  % (30825)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(resolution,[],[f11,f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f2])).
% 0.20/0.44  fof(f2,axiom,(
% 0.20/0.44    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(definition_unfolding,[],[f8,f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f1])).
% 0.20/0.44  fof(f1,axiom,(
% 0.20/0.44    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.44  fof(f8,plain,(
% 0.20/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(cnf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,plain,(
% 0.20/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f6])).
% 0.20/0.44  fof(f6,plain,(
% 0.20/0.44    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f5,plain,(
% 0.20/0.44    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f4])).
% 0.20/0.44  fof(f4,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f3])).
% 0.20/0.44  fof(f3,conjecture,(
% 0.20/0.44    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (30825)------------------------------
% 0.20/0.44  % (30825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (30825)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (30825)Memory used [KB]: 6012
% 0.20/0.44  % (30825)Time elapsed: 0.023 s
% 0.20/0.44  % (30825)------------------------------
% 0.20/0.44  % (30825)------------------------------
% 0.20/0.44  % (30810)Success in time 0.091 s
%------------------------------------------------------------------------------
