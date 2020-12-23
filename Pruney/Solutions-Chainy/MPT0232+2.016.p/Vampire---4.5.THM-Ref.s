%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:02 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   36 (  91 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 140 expanded)
%              Number of equality atoms :   24 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f66,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f20,f27,f21])).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f66,plain,(
    ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1)) ),
    inference(backward_demodulation,[],[f38,f60])).

fof(f60,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)) ),
    inference(resolution,[],[f42,f30])).

fof(f42,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k1_enumset1(sK0,sK0,sK1))
      | r1_tarski(X2,k1_enumset1(sK2,sK2,sK2)) ) ),
    inference(resolution,[],[f26,f29])).

fof(f29,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f17,f21,f27])).

fof(f17,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X1) != k1_tarski(X2)
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f22,f27,f27])).

fof(f22,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f38,plain,(
    ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)) ),
    inference(subsumption_resolution,[],[f34,f29])).

fof(f34,plain,
    ( ~ r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))
    | ~ r1_tarski(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)) ),
    inference(extensionality_resolution,[],[f25,f28])).

fof(f28,plain,(
    k1_enumset1(sK0,sK0,sK1) != k1_enumset1(sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f18,f21,f27])).

fof(f18,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n010.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 13:14:29 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.44  % (13659)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.16/0.45  % (13659)Refutation found. Thanks to Tanya!
% 0.16/0.45  % SZS status Theorem for theBenchmark
% 0.16/0.46  % (13667)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.16/0.46  % SZS output start Proof for theBenchmark
% 0.16/0.46  fof(f71,plain,(
% 0.16/0.46    $false),
% 0.16/0.46    inference(subsumption_resolution,[],[f66,f30])).
% 0.16/0.46  fof(f30,plain,(
% 0.16/0.46    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X1))) )),
% 0.16/0.46    inference(definition_unfolding,[],[f20,f27,f21])).
% 0.16/0.46  fof(f21,plain,(
% 0.16/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f4])).
% 0.16/0.46  fof(f4,axiom,(
% 0.16/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.16/0.46  fof(f27,plain,(
% 0.16/0.46    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.16/0.46    inference(definition_unfolding,[],[f19,f21])).
% 0.16/0.46  fof(f19,plain,(
% 0.16/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f3])).
% 0.16/0.46  fof(f3,axiom,(
% 0.16/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.16/0.46  fof(f20,plain,(
% 0.16/0.46    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f5])).
% 0.16/0.46  fof(f5,axiom,(
% 0.16/0.46    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.16/0.46  fof(f66,plain,(
% 0.16/0.46    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK1))),
% 0.16/0.46    inference(backward_demodulation,[],[f38,f60])).
% 0.16/0.46  fof(f60,plain,(
% 0.16/0.46    sK0 = sK2),
% 0.16/0.46    inference(resolution,[],[f31,f46])).
% 0.16/0.46  fof(f46,plain,(
% 0.16/0.46    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2))),
% 0.16/0.46    inference(resolution,[],[f42,f30])).
% 0.16/0.46  fof(f42,plain,(
% 0.16/0.46    ( ! [X2] : (~r1_tarski(X2,k1_enumset1(sK0,sK0,sK1)) | r1_tarski(X2,k1_enumset1(sK2,sK2,sK2))) )),
% 0.16/0.46    inference(resolution,[],[f26,f29])).
% 0.16/0.46  fof(f29,plain,(
% 0.16/0.46    r1_tarski(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))),
% 0.16/0.46    inference(definition_unfolding,[],[f17,f21,f27])).
% 0.16/0.46  fof(f17,plain,(
% 0.16/0.46    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.16/0.46    inference(cnf_transformation,[],[f14])).
% 0.16/0.46  fof(f14,plain,(
% 0.16/0.46    k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.16/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.16/0.46  fof(f13,plain,(
% 0.16/0.46    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (k2_tarski(sK0,sK1) != k1_tarski(sK2) & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 0.16/0.46    introduced(choice_axiom,[])).
% 0.16/0.46  fof(f9,plain,(
% 0.16/0.46    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.16/0.46    inference(ennf_transformation,[],[f8])).
% 0.16/0.46  fof(f8,negated_conjecture,(
% 0.16/0.46    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.16/0.46    inference(negated_conjecture,[],[f7])).
% 0.16/0.46  fof(f7,conjecture,(
% 0.16/0.46    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.16/0.46  fof(f26,plain,(
% 0.16/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f12])).
% 0.16/0.46  fof(f12,plain,(
% 0.16/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.16/0.46    inference(flattening,[],[f11])).
% 0.16/0.46  fof(f11,plain,(
% 0.16/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.16/0.46    inference(ennf_transformation,[],[f2])).
% 0.16/0.46  fof(f2,axiom,(
% 0.16/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.16/0.46  fof(f31,plain,(
% 0.16/0.46    ( ! [X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 = X1) )),
% 0.16/0.46    inference(definition_unfolding,[],[f22,f27,f27])).
% 0.16/0.46  fof(f22,plain,(
% 0.16/0.46    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1))) )),
% 0.16/0.46    inference(cnf_transformation,[],[f10])).
% 0.16/0.46  fof(f10,plain,(
% 0.16/0.46    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 0.16/0.46    inference(ennf_transformation,[],[f6])).
% 0.16/0.46  fof(f6,axiom,(
% 0.16/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 0.16/0.46  fof(f38,plain,(
% 0.16/0.46    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1))),
% 0.16/0.46    inference(subsumption_resolution,[],[f34,f29])).
% 0.16/0.46  fof(f34,plain,(
% 0.16/0.46    ~r1_tarski(k1_enumset1(sK2,sK2,sK2),k1_enumset1(sK0,sK0,sK1)) | ~r1_tarski(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2))),
% 0.16/0.46    inference(extensionality_resolution,[],[f25,f28])).
% 0.16/0.46  fof(f28,plain,(
% 0.16/0.46    k1_enumset1(sK0,sK0,sK1) != k1_enumset1(sK2,sK2,sK2)),
% 0.16/0.46    inference(definition_unfolding,[],[f18,f21,f27])).
% 0.16/0.46  fof(f18,plain,(
% 0.16/0.46    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.16/0.46    inference(cnf_transformation,[],[f14])).
% 0.16/0.46  fof(f25,plain,(
% 0.16/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.16/0.46    inference(cnf_transformation,[],[f16])).
% 0.16/0.46  fof(f16,plain,(
% 0.16/0.46    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.16/0.46    inference(flattening,[],[f15])).
% 0.16/0.46  fof(f15,plain,(
% 0.16/0.46    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.16/0.46    inference(nnf_transformation,[],[f1])).
% 0.16/0.46  fof(f1,axiom,(
% 0.16/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.16/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.16/0.46  % SZS output end Proof for theBenchmark
% 0.16/0.46  % (13659)------------------------------
% 0.16/0.46  % (13659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.46  % (13659)Termination reason: Refutation
% 0.16/0.46  
% 0.16/0.46  % (13659)Memory used [KB]: 10618
% 0.16/0.46  % (13659)Time elapsed: 0.094 s
% 0.16/0.46  % (13659)------------------------------
% 0.16/0.46  % (13659)------------------------------
% 0.16/0.46  % (13652)Success in time 0.137 s
%------------------------------------------------------------------------------
