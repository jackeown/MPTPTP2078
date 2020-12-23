%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   30 (  30 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  55 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f100])).

fof(f100,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f15,f86])).

fof(f86,plain,(
    ! [X3] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X3) ),
    inference(resolution,[],[f84,f20])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f84,plain,(
    ! [X4,X5] : ~ r2_hidden(X4,k10_relat_1(k1_xboole_0,X5)) ),
    inference(subsumption_resolution,[],[f80,f27])).

fof(f27,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f17,f16])).

fof(f16,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f17,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f80,plain,(
    ! [X4,X5] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X4,k10_relat_1(k1_xboole_0,X5)) ) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f29,f18])).

fof(f18,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

% (28153)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f15,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (28151)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % (28157)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (28151)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f100])).
% 0.22/0.42  fof(f100,plain,(
% 0.22/0.42    k1_xboole_0 != k1_xboole_0),
% 0.22/0.42    inference(superposition,[],[f15,f86])).
% 0.22/0.42  fof(f86,plain,(
% 0.22/0.42    ( ! [X3] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X3)) )),
% 0.22/0.42    inference(resolution,[],[f84,f20])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.42    inference(cnf_transformation,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.42  fof(f84,plain,(
% 0.22/0.42    ( ! [X4,X5] : (~r2_hidden(X4,k10_relat_1(k1_xboole_0,X5))) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f80,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    v1_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(superposition,[],[f17,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,axiom,(
% 0.22/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.22/0.42  fof(f80,plain,(
% 0.22/0.42    ( ! [X4,X5] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X4,k10_relat_1(k1_xboole_0,X5))) )),
% 0.22/0.42    inference(resolution,[],[f24,f30])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.22/0.42    inference(subsumption_resolution,[],[f29,f18])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f4])).
% 0.22/0.42  % (28153)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.42    inference(superposition,[],[f21,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(ennf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    inference(rectify,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK3(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(ennf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,negated_conjecture,(
% 0.22/0.42    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    inference(negated_conjecture,[],[f8])).
% 0.22/0.42  fof(f8,conjecture,(
% 0.22/0.42    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (28151)------------------------------
% 0.22/0.42  % (28151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (28151)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (28151)Memory used [KB]: 10618
% 0.22/0.42  % (28151)Time elapsed: 0.007 s
% 0.22/0.42  % (28151)------------------------------
% 0.22/0.42  % (28151)------------------------------
% 0.22/0.43  % (28150)Success in time 0.063 s
%------------------------------------------------------------------------------
