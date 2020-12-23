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
% DateTime   : Thu Dec  3 12:42:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   13 (  16 expanded)
%              Number of leaves         :    3 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   14 (  19 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f8])).

fof(f8,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f16,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f15,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f12,f9])).

fof(f12,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3))) ),
    inference(superposition,[],[f6,f7])).

fof(f7,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f6,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:53:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.21/0.43  % (9643)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.44  % (9637)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (9637)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(subsumption_resolution,[],[f16,f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_zfmisc_1(sK0,k2_xboole_0(sK2,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3)))),
% 0.21/0.44    inference(forward_demodulation,[],[f15,f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,k2_xboole_0(sK2,sK3)))),
% 0.21/0.44    inference(forward_demodulation,[],[f12,f9])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK1,sK3)))),
% 0.21/0.44    inference(superposition,[],[f6,f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    k2_zfmisc_1(k2_xboole_0(sK0,sK1),k2_xboole_0(sK2,sK3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK3)),k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK3))),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3))),
% 0.21/0.44    inference(negated_conjecture,[],[f3])).
% 0.21/0.44  fof(f3,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X3)),k2_zfmisc_1(X1,X2)),k2_zfmisc_1(X1,X3))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_zfmisc_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (9637)------------------------------
% 0.21/0.44  % (9637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (9637)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (9637)Memory used [KB]: 10490
% 0.21/0.44  % (9637)Time elapsed: 0.004 s
% 0.21/0.44  % (9637)------------------------------
% 0.21/0.44  % (9637)------------------------------
% 0.23/0.44  % (9635)Success in time 0.073 s
%------------------------------------------------------------------------------
