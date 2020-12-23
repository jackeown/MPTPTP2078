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
% DateTime   : Thu Dec  3 12:37:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  47 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  87 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f23])).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f32,plain,(
    ~ r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(backward_demodulation,[],[f30,f31])).

fof(f31,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f24,f22])).

fof(f22,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f13,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f20,f16])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f30,plain,(
    ~ r1_tarski(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f28,f21])).

fof(f21,plain,(
    k1_tarski(sK2) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,
    ( k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_tarski(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(resolution,[],[f19,f22])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:04:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (3402)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (3402)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f32,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f15,f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~r1_tarski(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.50    inference(backward_demodulation,[],[f30,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    sK0 = sK2),
% 0.21/0.50    inference(resolution,[],[f24,f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2))),
% 0.21/0.50    inference(definition_unfolding,[],[f13,f16])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) | X0 = X2) )),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f16])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ~r1_tarski(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f28,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    k1_tarski(sK2) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 0.21/0.50    inference(definition_unfolding,[],[f14,f16])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    k1_tarski(sK2) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_tarski(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 0.21/0.50    inference(resolution,[],[f19,f22])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3402)------------------------------
% 0.21/0.50  % (3402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3402)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3402)Memory used [KB]: 6140
% 0.21/0.50  % (3402)Time elapsed: 0.089 s
% 0.21/0.50  % (3402)------------------------------
% 0.21/0.50  % (3402)------------------------------
% 0.21/0.51  % (3379)Success in time 0.139 s
%------------------------------------------------------------------------------
