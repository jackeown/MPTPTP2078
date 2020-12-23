%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   34 ( 120 expanded)
%              Number of leaves         :    3 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 254 expanded)
%              Number of equality atoms :   51 ( 210 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f57,f45])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f7,f41])).

fof(f41,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f37,f7])).

fof(f37,plain,
    ( sK0 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f13,f9])).

fof(f9,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f35,plain,(
    r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f26,f16])).

fof(f16,plain,(
    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f6,f9,f9])).

fof(f6,plain,(
    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & k2_tarski(X0,X1) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).

fof(f26,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f14,f9])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f54,f26])).

fof(f54,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1))
      | sK1 = X3 ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X3] :
      ( sK1 = X3
      | sK1 = X3
      | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f43,f50])).

fof(f50,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f46,f8])).

fof(f8,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,
    ( sK0 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f36,f27])).

fof(f36,plain,(
    r2_hidden(sK3,k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f24,f16])).

fof(f24,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_enumset1(X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f15,f9])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X3] :
      ( sK1 = X3
      | ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1))
      | sK3 = X3 ) ),
    inference(backward_demodulation,[],[f34,f41])).

fof(f34,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1))
      | sK2 = X3
      | sK3 = X3 ) ),
    inference(superposition,[],[f27,f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (28022)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (28038)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (28022)Refutation not found, incomplete strategy% (28022)------------------------------
% 0.22/0.52  % (28022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28022)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28022)Memory used [KB]: 1663
% 0.22/0.52  % (28022)Time elapsed: 0.101 s
% 0.22/0.52  % (28022)------------------------------
% 0.22/0.52  % (28022)------------------------------
% 0.22/0.52  % (28038)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f57,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    sK0 != sK1),
% 0.22/0.52    inference(superposition,[],[f7,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    sK1 = sK2),
% 0.22/0.52    inference(subsumption_resolution,[],[f37,f7])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    sK0 = sK2 | sK1 = sK2),
% 0.22/0.52    inference(resolution,[],[f35,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f13,f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    r2_hidden(sK2,k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.22/0.52    inference(superposition,[],[f26,f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    k2_enumset1(sK0,sK0,sK0,sK1) = k2_enumset1(sK2,sK2,sK2,sK3)),
% 0.22/0.52    inference(definition_unfolding,[],[f6,f9,f9])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,plain,(
% 0.22/0.52    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.22/0.52    inference(negated_conjecture,[],[f3])).
% 0.22/0.52  fof(f3,conjecture,(
% 0.22/0.52    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & k2_tarski(X0,X1) = k2_tarski(X2,X3))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_zfmisc_1)).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.22/0.52    inference(equality_resolution,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f14,f9])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    sK0 != sK2),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    sK0 = sK1),
% 0.22/0.52    inference(resolution,[],[f54,f26])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1)) | sK1 = X3) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X3] : (sK1 = X3 | sK1 = X3 | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1))) )),
% 0.22/0.52    inference(backward_demodulation,[],[f43,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    sK1 = sK3),
% 0.22/0.52    inference(subsumption_resolution,[],[f46,f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    sK0 != sK3),
% 0.22/0.52    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    sK0 = sK3 | sK1 = sK3),
% 0.22/0.52    inference(resolution,[],[f36,f27])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    r2_hidden(sK3,k2_enumset1(sK0,sK0,sK0,sK1))),
% 0.22/0.52    inference(superposition,[],[f24,f16])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ( ! [X0,X3] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X3))) )),
% 0.22/0.52    inference(equality_resolution,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X3) != X2) )),
% 0.22/0.52    inference(equality_resolution,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.22/0.52    inference(definition_unfolding,[],[f15,f9])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X3] : (sK1 = X3 | ~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1)) | sK3 = X3) )),
% 0.22/0.52    inference(backward_demodulation,[],[f34,f41])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X3] : (~r2_hidden(X3,k2_enumset1(sK0,sK0,sK0,sK1)) | sK2 = X3 | sK3 = X3) )),
% 0.22/0.52    inference(superposition,[],[f27,f16])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28038)------------------------------
% 0.22/0.52  % (28038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28038)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28038)Memory used [KB]: 1663
% 0.22/0.52  % (28038)Time elapsed: 0.120 s
% 0.22/0.52  % (28038)------------------------------
% 0.22/0.52  % (28038)------------------------------
% 0.22/0.52  % (28020)Success in time 0.161 s
%------------------------------------------------------------------------------
