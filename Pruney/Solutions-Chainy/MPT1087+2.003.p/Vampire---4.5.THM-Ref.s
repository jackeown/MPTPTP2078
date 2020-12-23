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
% DateTime   : Thu Dec  3 13:08:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of leaves         :    5 (   8 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  50 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    $false ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    ~ v1_finset_1(k1_setfam_1(k2_tarski(sK0,sK1))) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f12,plain,(
    ~ v1_finset_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
    & v1_finset_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(k3_xboole_0(X0,X1))
        & v1_finset_1(X0) )
   => ( ~ v1_finset_1(k3_xboole_0(sK0,sK1))
      & v1_finset_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(k3_xboole_0(X0,X1))
      & v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_finset_1(X0)
       => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
     => v1_finset_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).

fof(f19,plain,(
    ! [X0] : v1_finset_1(k1_setfam_1(k2_tarski(sK0,X0))) ),
    inference(resolution,[],[f18,f11])).

fof(f11,plain,(
    v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X0)
      | v1_finset_1(k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(resolution,[],[f15,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_finset_1(X1)
      | v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X0)
      | ~ v1_finset_1(X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (11036)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.41  % (11036)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(resolution,[],[f19,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ~v1_finset_1(k1_setfam_1(k2_tarski(sK0,sK1)))),
% 0.21/0.41    inference(definition_unfolding,[],[f12,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ~v1_finset_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0)) => (~v1_finset_1(k3_xboole_0(sK0,sK1)) & v1_finset_1(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0,X1] : (~v1_finset_1(k3_xboole_0(X0,X1)) & v1_finset_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,negated_conjecture,(
% 0.21/0.41    ~! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.41    inference(negated_conjecture,[],[f4])).
% 0.21/0.41  fof(f4,conjecture,(
% 0.21/0.41    ! [X0,X1] : (v1_finset_1(X0) => v1_finset_1(k3_xboole_0(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0] : (v1_finset_1(k1_setfam_1(k2_tarski(sK0,X0)))) )),
% 0.21/0.41    inference(resolution,[],[f18,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    v1_finset_1(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v1_finset_1(X0) | v1_finset_1(k1_setfam_1(k2_tarski(X0,X1)))) )),
% 0.21/0.41    inference(resolution,[],[f15,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.21/0.41    inference(definition_unfolding,[],[f13,f14])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_finset_1(X1) | v1_finset_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_finset_1(X0) | ~v1_finset_1(X1) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_finset_1(X0) | (~v1_finset_1(X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_finset_1(X1) & r1_tarski(X0,X1)) => v1_finset_1(X0))),
% 0.21/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (11036)------------------------------
% 0.21/0.41  % (11036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (11036)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.42  % (11036)Memory used [KB]: 1535
% 0.21/0.42  % (11036)Time elapsed: 0.003 s
% 0.21/0.42  % (11036)------------------------------
% 0.21/0.42  % (11036)------------------------------
% 0.21/0.42  % (11023)Success in time 0.06 s
%------------------------------------------------------------------------------
