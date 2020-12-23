%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:39 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   17 (  20 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  34 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,plain,(
    $false ),
    inference(resolution,[],[f18,f11])).

fof(f11,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).

fof(f7,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f13,f15])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = sK1(X0) ),
    inference(resolution,[],[f12,f14])).

fof(f14,plain,(
    ! [X0] : v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f13,plain,(
    ! [X0] : m1_subset_1(sK1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:32:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (31914)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.13/0.41  % (31910)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.13/0.41  % (31910)Refutation found. Thanks to Tanya!
% 0.13/0.41  % SZS status Theorem for theBenchmark
% 0.13/0.41  % SZS output start Proof for theBenchmark
% 0.13/0.41  fof(f19,plain,(
% 0.13/0.41    $false),
% 0.13/0.41    inference(resolution,[],[f18,f11])).
% 0.13/0.41  fof(f11,plain,(
% 0.13/0.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.13/0.41    inference(cnf_transformation,[],[f8])).
% 0.13/0.41  fof(f8,plain,(
% 0.13/0.41    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f5,f7])).
% 0.13/0.41  fof(f7,plain,(
% 0.13/0.41    ? [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) => ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f5,plain,(
% 0.13/0.41    ? [X0] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f4])).
% 0.13/0.41  fof(f4,negated_conjecture,(
% 0.13/0.41    ~! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.13/0.41    inference(negated_conjecture,[],[f3])).
% 0.13/0.41  fof(f3,conjecture,(
% 0.13/0.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.13/0.41  fof(f18,plain,(
% 0.13/0.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(superposition,[],[f13,f15])).
% 0.13/0.41  fof(f15,plain,(
% 0.13/0.41    ( ! [X0] : (k1_xboole_0 = sK1(X0)) )),
% 0.13/0.41    inference(resolution,[],[f12,f14])).
% 0.13/0.41  fof(f14,plain,(
% 0.13/0.41    ( ! [X0] : (v1_xboole_0(sK1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f10])).
% 0.13/0.41  fof(f10,plain,(
% 0.13/0.41    ! [X0] : (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0)))),
% 0.13/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f2,f9])).
% 0.13/0.41  fof(f9,plain,(
% 0.13/0.41    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(X0))))),
% 0.13/0.41    introduced(choice_axiom,[])).
% 0.13/0.41  fof(f2,axiom,(
% 0.13/0.41    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).
% 0.13/0.41  fof(f12,plain,(
% 0.13/0.41    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.13/0.41    inference(cnf_transformation,[],[f6])).
% 0.13/0.41  fof(f6,plain,(
% 0.13/0.41    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.13/0.41    inference(ennf_transformation,[],[f1])).
% 0.13/0.41  fof(f1,axiom,(
% 0.13/0.41    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.13/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).
% 0.13/0.41  fof(f13,plain,(
% 0.13/0.41    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(X0))) )),
% 0.13/0.41    inference(cnf_transformation,[],[f10])).
% 0.13/0.41  % SZS output end Proof for theBenchmark
% 0.13/0.41  % (31910)------------------------------
% 0.13/0.41  % (31910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.41  % (31910)Termination reason: Refutation
% 0.13/0.41  
% 0.13/0.41  % (31910)Memory used [KB]: 6012
% 0.13/0.41  % (31910)Time elapsed: 0.003 s
% 0.13/0.41  % (31910)------------------------------
% 0.13/0.41  % (31910)------------------------------
% 0.13/0.42  % (31905)Success in time 0.061 s
%------------------------------------------------------------------------------
