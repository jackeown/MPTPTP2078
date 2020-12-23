%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :    9 (  20 expanded)
%              Depth                    :   21
%              Number of atoms          :  102 ( 193 expanded)
%              Number of equality atoms :   66 ( 131 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(subsumption_resolution,[],[f152,f38])).

fof(f38,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f152,plain,(
    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f53,f146])).

fof(f146,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f144,f45])).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f144,plain,(
    ! [X1] :
      ( ~ r1_tarski(k3_xboole_0(X1,k1_tarski(sK0)),sK1)
      | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f140,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f140,plain,(
    ! [X0] :
      ( ~ r1_tarski(k3_xboole_0(k1_tarski(sK0),X0),sK1)
      | k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),X0) ) ),
    inference(resolution,[],[f137,f45])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tarski(sK0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f132,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f132,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k1_tarski(sK0) ),
    inference(resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(sK0))
      | ~ r1_tarski(k1_tarski(X0),sK1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(sK0))
      | ~ r1_tarski(k1_tarski(X0),sK1)
      | k1_xboole_0 = k1_tarski(X0)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f108,f51])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,k1_tarski(sK0))
      | ~ r1_tarski(X0,sK1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f103,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k1_tarski(sK0))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f92,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f92,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k5_xboole_0(X2,k3_xboole_0(X2,sK1))
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f66,f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(sK1,X1))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(sK0)) ) ),
    inference(superposition,[],[f55,f35])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tarski(sK0))
      | k1_xboole_0 = X0
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(sK1,X0)) ) ),
    inference(superposition,[],[f54,f35])).

fof(f54,plain,(
    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f47,f40])).

fof(f47,plain,(
    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f30,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
        & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) )
   => ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f53,plain,(
    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f46,f40])).

fof(f46,plain,(
    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f31,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:41:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (6154)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.48  % (6154)Refutation not found, incomplete strategy% (6154)------------------------------
% 0.22/0.48  % (6154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (6146)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.48  % (6154)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (6154)Memory used [KB]: 10618
% 0.22/0.48  % (6154)Time elapsed: 0.060 s
% 0.22/0.48  % (6154)------------------------------
% 0.22/0.48  % (6154)------------------------------
% 0.22/0.49  % (6146)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f153,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f152,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.22/0.49    inference(backward_demodulation,[],[f53,f146])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.49    inference(resolution,[],[f144,f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ( ! [X1] : (~r1_tarski(k3_xboole_0(X1,k1_tarski(sK0)),sK1) | k1_xboole_0 = k3_xboole_0(X1,k1_tarski(sK0))) )),
% 0.22/0.49    inference(superposition,[],[f140,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(k3_xboole_0(k1_tarski(sK0),X0),sK1) | k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),X0)) )),
% 0.22/0.49    inference(resolution,[],[f137,f45])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k1_tarski(sK0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,sK1)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f136])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(sK0))) )),
% 0.22/0.49    inference(superposition,[],[f132,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.49    inference(nnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ~r1_tarski(k1_tarski(sK0),sK1) | k1_xboole_0 = k1_tarski(sK0)),
% 0.22/0.49    inference(resolution,[],[f128,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) != X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k1_tarski(sK0)) | ~r1_tarski(k1_tarski(X0),sK1) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f116])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(k1_tarski(X0),k1_tarski(sK0)) | ~r1_tarski(k1_tarski(X0),sK1) | k1_xboole_0 = k1_tarski(X0) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.49    inference(resolution,[],[f108,f51])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,k1_tarski(sK0)) | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f103,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k1_tarski(sK0)) | ~r1_tarski(X0,sK1)) )),
% 0.22/0.49    inference(superposition,[],[f92,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k1_xboole_0 != k5_xboole_0(X2,k3_xboole_0(X2,sK1)) | k1_xboole_0 = X2 | ~r1_tarski(X2,X3) | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_tarski(sK0))) )),
% 0.22/0.49    inference(superposition,[],[f66,f40])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(sK1,X1)) | k1_xboole_0 = X1 | ~r1_tarski(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(sK0))) )),
% 0.22/0.49    inference(superposition,[],[f55,f35])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(X0,k1_tarski(sK0)) | k1_xboole_0 = X0 | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(sK1,X0))) )),
% 0.22/0.49    inference(superposition,[],[f54,f35])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k1_tarski(sK0)))),
% 0.22/0.49    inference(forward_demodulation,[],[f47,f40])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    k1_xboole_0 != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK1))),
% 0.22/0.49    inference(definition_unfolding,[],[f30,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) => (k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) & k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f22])).
% 0.22/0.49  fof(f22,conjecture,(
% 0.22/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(sK1,k1_tarski(sK0)))),
% 0.22/0.49    inference(forward_demodulation,[],[f46,f40])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    k1_tarski(sK0) != k5_xboole_0(k1_tarski(sK0),k3_xboole_0(k1_tarski(sK0),sK1))),
% 0.22/0.49    inference(definition_unfolding,[],[f31,f34])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (6146)------------------------------
% 0.22/0.49  % (6146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (6146)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (6146)Memory used [KB]: 1791
% 0.22/0.49  % (6146)Time elapsed: 0.064 s
% 0.22/0.49  % (6146)------------------------------
% 0.22/0.49  % (6146)------------------------------
% 0.22/0.49  % (6145)Success in time 0.124 s
%------------------------------------------------------------------------------
