%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :    5 (   7 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) ),
    inference(superposition,[],[f12,f30])).

fof(f30,plain,(
    ! [X1] : k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1) ),
    inference(superposition,[],[f16,f20])).

fof(f20,plain,(
    sK1 = k4_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f18,f11])).

fof(f11,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
        & r1_xboole_0(X0,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0)
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f14,f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

% (22998)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f16,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f12,plain,(
    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:01:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (22996)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.44  % (22996)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k2_xboole_0(k4_xboole_0(sK2,sK0),sK1)),
% 0.21/0.44    inference(superposition,[],[f12,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ( ! [X1] : (k4_xboole_0(k2_xboole_0(X1,sK1),sK0) = k2_xboole_0(k4_xboole_0(X1,sK0),sK1)) )),
% 0.21/0.44    inference(superposition,[],[f16,f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    sK1 = k4_xboole_0(sK1,sK0)),
% 0.21/0.44    inference(resolution,[],[f18,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1)) => (k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0) & r1_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X2,X0),X1) != k4_xboole_0(k2_xboole_0(X2,X1),X0) & r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.44    inference(negated_conjecture,[],[f4])).
% 0.21/0.44  fof(f4,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k2_xboole_0(k4_xboole_0(X2,X0),X1) = k4_xboole_0(k2_xboole_0(X2,X1),X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.44    inference(resolution,[],[f14,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(nnf_transformation,[],[f3])).
% 0.21/0.44  % (22998)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k2_xboole_0(k4_xboole_0(sK2,sK0),sK1) != k4_xboole_0(k2_xboole_0(sK2,sK1),sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (22996)------------------------------
% 0.21/0.44  % (22996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (22996)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (22996)Memory used [KB]: 6140
% 0.21/0.44  % (22996)Time elapsed: 0.005 s
% 0.21/0.44  % (22996)------------------------------
% 0.21/0.44  % (22996)------------------------------
% 0.21/0.44  % (22991)Success in time 0.076 s
%------------------------------------------------------------------------------
