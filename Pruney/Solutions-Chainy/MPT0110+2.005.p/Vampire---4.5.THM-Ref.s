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
% DateTime   : Thu Dec  3 12:32:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :    9 (   9 expanded)
%              Number of leaves         :    3 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,plain,(
    $false ),
    inference(resolution,[],[f8,f7])).

fof(f7,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).

fof(f5,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))
   => ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f4,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

fof(f8,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:34:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (2681)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.48  % (2680)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.49  % (2689)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.20/0.49  % (2681)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(resolution,[],[f8,f7])).
% 0.20/0.49  fof(f7,plain,(
% 0.20/0.49    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,plain,(
% 0.20/0.49    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).
% 0.20/0.49  fof(f5,plain,(
% 0.20/0.49    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) => ~r1_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f4,plain,(
% 0.20/0.49    ? [X0,X1] : ~r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f2])).
% 0.20/0.49  fof(f2,conjecture,(
% 0.20/0.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (2681)------------------------------
% 0.20/0.49  % (2681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2681)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (2681)Memory used [KB]: 5245
% 0.20/0.49  % (2681)Time elapsed: 0.065 s
% 0.20/0.49  % (2681)------------------------------
% 0.20/0.49  % (2681)------------------------------
% 0.20/0.49  % (2682)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (2673)Success in time 0.127 s
%------------------------------------------------------------------------------
