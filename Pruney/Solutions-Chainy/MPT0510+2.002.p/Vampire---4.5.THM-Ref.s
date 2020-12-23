%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   24 (  62 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   31 (  96 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,(
    k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f10,f102])).

fof(f102,plain,(
    ! [X2,X3] : k7_relat_1(sK2,k3_xboole_0(X2,X3)) = k3_xboole_0(k7_relat_1(sK2,X2),k7_relat_1(sK2,X3)) ),
    inference(superposition,[],[f53,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(k7_relat_1(sK2,X0),k2_zfmisc_1(X1,k2_relat_1(sK2))) = k7_relat_1(sK2,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f89,f19])).

fof(f19,plain,(
    ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))) ),
    inference(resolution,[],[f11,f9])).

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(k7_relat_1(sK2,X0),k2_zfmisc_1(X1,k2_relat_1(sK2))) = k3_xboole_0(sK2,k2_zfmisc_1(k3_xboole_0(X0,X1),k2_relat_1(sK2))) ),
    inference(superposition,[],[f20,f14])).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1)) = k3_xboole_0(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[],[f12,f19])).

fof(f12,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(k7_relat_1(sK2,X1),k2_zfmisc_1(X0,k2_relat_1(sK2))) = k3_xboole_0(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0)) ),
    inference(superposition,[],[f40,f19])).

fof(f40,plain,(
    ! [X8,X9] : k3_xboole_0(k7_relat_1(sK2,X8),k3_xboole_0(sK2,X9)) = k3_xboole_0(k7_relat_1(sK2,X8),X9) ),
    inference(forward_demodulation,[],[f26,f20])).

fof(f26,plain,(
    ! [X8,X9] : k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X8,k2_relat_1(sK2)),X9)) = k3_xboole_0(k7_relat_1(sK2,X8),k3_xboole_0(sK2,X9)) ),
    inference(superposition,[],[f13,f19])).

fof(f13,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).

fof(f10,plain,(
    k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:07:02 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (8781)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.42  % (8788)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.42  % (8781)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(trivial_inequality_removal,[],[f110])).
% 0.22/0.42  fof(f110,plain,(
% 0.22/0.42    k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k7_relat_1(sK2,k3_xboole_0(sK0,sK1))),
% 0.22/0.42    inference(superposition,[],[f10,f102])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    ( ! [X2,X3] : (k7_relat_1(sK2,k3_xboole_0(X2,X3)) = k3_xboole_0(k7_relat_1(sK2,X2),k7_relat_1(sK2,X3))) )),
% 0.22/0.42    inference(superposition,[],[f53,f94])).
% 0.22/0.42  fof(f94,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(k7_relat_1(sK2,X0),k2_zfmisc_1(X1,k2_relat_1(sK2))) = k7_relat_1(sK2,k3_xboole_0(X0,X1))) )),
% 0.22/0.42    inference(forward_demodulation,[],[f89,f19])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ( ! [X0] : (k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))) )),
% 0.22/0.42    inference(resolution,[],[f11,f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    v1_relat_1(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) != k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) & v1_relat_1(X2))),
% 0.22/0.42    inference(ennf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.42    inference(negated_conjecture,[],[f5])).
% 0.22/0.42  fof(f5,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 0.22/0.42  fof(f89,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(k7_relat_1(sK2,X0),k2_zfmisc_1(X1,k2_relat_1(sK2))) = k3_xboole_0(sK2,k2_zfmisc_1(k3_xboole_0(X0,X1),k2_relat_1(sK2)))) )),
% 0.22/0.42    inference(superposition,[],[f20,f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X0,k2_relat_1(sK2)),X1)) = k3_xboole_0(k7_relat_1(sK2,X0),X1)) )),
% 0.22/0.42    inference(superposition,[],[f12,f19])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(k7_relat_1(sK2,X1),k2_zfmisc_1(X0,k2_relat_1(sK2))) = k3_xboole_0(k7_relat_1(sK2,X1),k7_relat_1(sK2,X0))) )),
% 0.22/0.42    inference(superposition,[],[f40,f19])).
% 0.22/0.42  fof(f40,plain,(
% 0.22/0.42    ( ! [X8,X9] : (k3_xboole_0(k7_relat_1(sK2,X8),k3_xboole_0(sK2,X9)) = k3_xboole_0(k7_relat_1(sK2,X8),X9)) )),
% 0.22/0.42    inference(forward_demodulation,[],[f26,f20])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ( ! [X8,X9] : (k3_xboole_0(sK2,k3_xboole_0(k2_zfmisc_1(X8,k2_relat_1(sK2)),X9)) = k3_xboole_0(k7_relat_1(sK2,X8),k3_xboole_0(sK2,X9))) )),
% 0.22/0.42    inference(superposition,[],[f13,f19])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_xboole_1)).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    k7_relat_1(sK2,k3_xboole_0(sK0,sK1)) != k3_xboole_0(k7_relat_1(sK2,sK0),k7_relat_1(sK2,sK1))),
% 0.22/0.42    inference(cnf_transformation,[],[f7])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (8781)------------------------------
% 0.22/0.42  % (8781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (8781)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (8781)Memory used [KB]: 10618
% 0.22/0.42  % (8781)Time elapsed: 0.008 s
% 0.22/0.42  % (8781)------------------------------
% 0.22/0.42  % (8781)------------------------------
% 0.22/0.43  % (8779)Success in time 0.065 s
%------------------------------------------------------------------------------
