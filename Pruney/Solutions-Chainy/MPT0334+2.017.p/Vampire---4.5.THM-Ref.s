%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  46 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  59 expanded)
%              Number of equality atoms :   21 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f17,f20,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0))))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X0)) ) ),
    inference(definition_unfolding,[],[f12,f16,f15,f15,f16])).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f20,plain,(
    r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f10,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f10,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( X0 != X1
       => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( X0 != X1
     => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

fof(f17,plain,(
    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))),k1_tarski(sK1))) != k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1)))))) ),
    inference(definition_unfolding,[],[f11,f15,f16,f16,f15])).

fof(f11,plain,(
    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:06:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8042)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (8042)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (8043)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f17,f20,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(k5_xboole_0(X2,k3_xboole_0(X2,X0)),k5_xboole_0(X1,k3_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X0))))) = k5_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))),k3_xboole_0(k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X1,X2))),X0))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f12,f16,f15,f15,f16])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f13,f15])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f10,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    sK0 != sK1),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) != k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)) & X0 != X1)),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f5])).
% 0.21/0.52  fof(f5,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (X0 != X1 => k4_xboole_0(k2_xboole_0(X2,k1_tarski(X0)),k1_tarski(X1)) = k2_xboole_0(k4_xboole_0(X2,k1_tarski(X1)),k1_tarski(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k5_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))),k3_xboole_0(k5_xboole_0(sK2,k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK2))),k1_tarski(sK1))) != k5_xboole_0(k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))),k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(sK2,k3_xboole_0(sK2,k1_tarski(sK1))))))),
% 0.21/0.52    inference(definition_unfolding,[],[f11,f15,f16,f16,f15])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    k4_xboole_0(k2_xboole_0(sK2,k1_tarski(sK0)),k1_tarski(sK1)) != k2_xboole_0(k4_xboole_0(sK2,k1_tarski(sK1)),k1_tarski(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (8042)------------------------------
% 0.21/0.52  % (8042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8042)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (8042)Memory used [KB]: 6140
% 0.21/0.52  % (8042)Time elapsed: 0.109 s
% 0.21/0.52  % (8042)------------------------------
% 0.21/0.52  % (8042)------------------------------
% 0.21/0.52  % (8035)Success in time 0.154 s
%------------------------------------------------------------------------------
