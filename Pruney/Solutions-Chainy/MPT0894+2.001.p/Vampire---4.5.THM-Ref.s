%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  15 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    6
%              Number of atoms          :   14 (  16 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12])).

fof(f12,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
    inference(definition_unfolding,[],[f8,f11,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f11,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f10,f9])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f8,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) != k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)
   => k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) != k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (7741)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.43  % (7741)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.22/0.43    inference(definition_unfolding,[],[f8,f11,f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.22/0.43    inference(definition_unfolding,[],[f10,f9])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) != k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) => k4_zfmisc_1(sK0,sK1,sK2,sK3) != k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3)),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f5,plain,(
% 0.22/0.43    ? [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) != k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)),
% 0.22/0.43    inference(negated_conjecture,[],[f3])).
% 0.22/0.43  fof(f3,conjecture,(
% 0.22/0.43    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_mcart_1)).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (7741)------------------------------
% 0.22/0.43  % (7741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (7741)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (7741)Memory used [KB]: 6012
% 0.22/0.43  % (7741)Time elapsed: 0.003 s
% 0.22/0.43  % (7741)------------------------------
% 0.22/0.43  % (7741)------------------------------
% 0.22/0.44  % (7726)Success in time 0.076 s
%------------------------------------------------------------------------------
