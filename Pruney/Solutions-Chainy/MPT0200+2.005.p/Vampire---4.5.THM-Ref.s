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
% DateTime   : Thu Dec  3 12:34:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   13 (  13 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    7
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f25])).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3) ),
    inference(superposition,[],[f11,f10])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).

fof(f11,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0) ),
    inference(superposition,[],[f8,f9])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).

fof(f8,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (6074)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.44  % (6070)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (6070)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK1,sK2,sK3)),
% 0.22/0.44    inference(superposition,[],[f11,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X2,X3,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_enumset1)).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK2,sK3,sK0)),
% 0.22/0.44    inference(superposition,[],[f8,f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X2,X1,X0,X3)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l129_enumset1)).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK3,sK2,sK1,sK0)),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f5,plain,(
% 0.22/0.44    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.44    inference(negated_conjecture,[],[f3])).
% 0.22/0.44  fof(f3,conjecture,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (6070)------------------------------
% 0.22/0.44  % (6070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (6070)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (6070)Memory used [KB]: 6012
% 0.22/0.44  % (6070)Time elapsed: 0.003 s
% 0.22/0.44  % (6070)------------------------------
% 0.22/0.44  % (6070)------------------------------
% 0.22/0.44  % (6065)Success in time 0.069 s
%------------------------------------------------------------------------------
