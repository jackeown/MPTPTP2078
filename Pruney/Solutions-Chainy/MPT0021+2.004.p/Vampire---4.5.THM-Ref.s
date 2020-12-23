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
% DateTime   : Thu Dec  3 12:29:36 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   30 (  56 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   12
%              Number of atoms          :   57 ( 149 expanded)
%              Number of equality atoms :   21 (  45 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f399,plain,(
    $false ),
    inference(subsumption_resolution,[],[f398,f13])).

fof(f13,plain,(
    sK1 != k2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,X2) != X1
      & ! [X3] :
          ( r1_tarski(X1,X3)
          | ~ r1_tarski(X2,X3)
          | ~ r1_tarski(X0,X3) )
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( ( r1_tarski(X2,X3)
                & r1_tarski(X0,X3) )
             => r1_tarski(X1,X3) )
          & r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => k2_xboole_0(X0,X2) = X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X2,X3)
              & r1_tarski(X0,X3) )
           => r1_tarski(X1,X3) )
        & r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => k2_xboole_0(X0,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).

fof(f398,plain,(
    sK1 = k2_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f397,f18])).

fof(f18,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f11,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f11,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f397,plain,(
    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f377,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f377,plain,(
    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f208,f139])).

fof(f139,plain,(
    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f126,f16])).

fof(f126,plain,(
    r1_tarski(sK1,k2_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f40,f14])).

fof(f14,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f40,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,k2_xboole_0(X1,sK2))
      | r1_tarski(sK1,k2_xboole_0(X1,sK2)) ) ),
    inference(superposition,[],[f37,f15])).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,k2_xboole_0(sK2,X0))
      | r1_tarski(sK1,k2_xboole_0(sK2,X0)) ) ),
    inference(resolution,[],[f10,f14])).

fof(f10,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK2,X3)
      | ~ r1_tarski(sK0,X3)
      | r1_tarski(sK1,X3) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f208,plain,(
    ! [X2] : k2_xboole_0(sK1,X2) = k2_xboole_0(sK1,k2_xboole_0(X2,sK2)) ),
    inference(superposition,[],[f30,f15])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(sK1,X0) = k2_xboole_0(sK1,k2_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f17,f23])).

fof(f23,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f19,f15])).

fof(f19,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f12,f16])).

fof(f12,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_vampire %s %d
% 0.15/0.37  % Computer   : n007.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % WCLimit    : 600
% 0.15/0.37  % DateTime   : Tue Dec  1 11:51:36 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.24/0.48  % (20627)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.24/0.49  % (20627)Refutation found. Thanks to Tanya!
% 0.24/0.49  % SZS status Theorem for theBenchmark
% 0.24/0.49  % (20618)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.24/0.49  % (20633)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.24/0.49  % SZS output start Proof for theBenchmark
% 0.24/0.49  fof(f399,plain,(
% 0.24/0.49    $false),
% 0.24/0.49    inference(subsumption_resolution,[],[f398,f13])).
% 0.24/0.49  fof(f13,plain,(
% 0.24/0.49    sK1 != k2_xboole_0(sK0,sK2)),
% 0.24/0.49    inference(cnf_transformation,[],[f8])).
% 0.24/0.49  fof(f8,plain,(
% 0.24/0.49    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & ! [X3] : (r1_tarski(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.24/0.49    inference(flattening,[],[f7])).
% 0.24/0.49  fof(f7,plain,(
% 0.24/0.49    ? [X0,X1,X2] : (k2_xboole_0(X0,X2) != X1 & (! [X3] : (r1_tarski(X1,X3) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X3))) & r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.24/0.49    inference(ennf_transformation,[],[f6])).
% 0.24/0.49  fof(f6,negated_conjecture,(
% 0.24/0.49    ~! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.24/0.49    inference(negated_conjecture,[],[f5])).
% 0.24/0.49  fof(f5,conjecture,(
% 0.24/0.49    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X3)) => r1_tarski(X1,X3)) & r1_tarski(X2,X1) & r1_tarski(X0,X1)) => k2_xboole_0(X0,X2) = X1)),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_xboole_1)).
% 0.24/0.49  fof(f398,plain,(
% 0.24/0.49    sK1 = k2_xboole_0(sK0,sK2)),
% 0.24/0.49    inference(forward_demodulation,[],[f397,f18])).
% 0.24/0.49  fof(f18,plain,(
% 0.24/0.49    sK1 = k2_xboole_0(sK0,sK1)),
% 0.24/0.49    inference(resolution,[],[f11,f16])).
% 0.24/0.49  fof(f16,plain,(
% 0.24/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.24/0.49    inference(cnf_transformation,[],[f9])).
% 0.24/0.49  fof(f9,plain,(
% 0.24/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.24/0.49    inference(ennf_transformation,[],[f2])).
% 0.24/0.49  fof(f2,axiom,(
% 0.24/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.24/0.49  fof(f11,plain,(
% 0.24/0.49    r1_tarski(sK0,sK1)),
% 0.24/0.49    inference(cnf_transformation,[],[f8])).
% 0.24/0.49  fof(f397,plain,(
% 0.24/0.49    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK0,sK1)),
% 0.24/0.49    inference(forward_demodulation,[],[f377,f15])).
% 0.24/0.49  fof(f15,plain,(
% 0.24/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f1])).
% 0.24/0.49  fof(f1,axiom,(
% 0.24/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.24/0.49  fof(f377,plain,(
% 0.24/0.49    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,sK0)),
% 0.24/0.49    inference(superposition,[],[f208,f139])).
% 0.24/0.49  fof(f139,plain,(
% 0.24/0.49    k2_xboole_0(sK0,sK2) = k2_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 0.24/0.49    inference(resolution,[],[f126,f16])).
% 0.24/0.49  fof(f126,plain,(
% 0.24/0.49    r1_tarski(sK1,k2_xboole_0(sK0,sK2))),
% 0.24/0.49    inference(resolution,[],[f40,f14])).
% 0.24/0.49  fof(f14,plain,(
% 0.24/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.24/0.49    inference(cnf_transformation,[],[f4])).
% 0.24/0.49  fof(f4,axiom,(
% 0.24/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.24/0.49  fof(f40,plain,(
% 0.24/0.49    ( ! [X1] : (~r1_tarski(sK0,k2_xboole_0(X1,sK2)) | r1_tarski(sK1,k2_xboole_0(X1,sK2))) )),
% 0.24/0.49    inference(superposition,[],[f37,f15])).
% 0.24/0.49  fof(f37,plain,(
% 0.24/0.49    ( ! [X0] : (~r1_tarski(sK0,k2_xboole_0(sK2,X0)) | r1_tarski(sK1,k2_xboole_0(sK2,X0))) )),
% 0.24/0.49    inference(resolution,[],[f10,f14])).
% 0.24/0.49  fof(f10,plain,(
% 0.24/0.49    ( ! [X3] : (~r1_tarski(sK2,X3) | ~r1_tarski(sK0,X3) | r1_tarski(sK1,X3)) )),
% 0.24/0.49    inference(cnf_transformation,[],[f8])).
% 0.24/0.49  fof(f208,plain,(
% 0.24/0.49    ( ! [X2] : (k2_xboole_0(sK1,X2) = k2_xboole_0(sK1,k2_xboole_0(X2,sK2))) )),
% 0.24/0.49    inference(superposition,[],[f30,f15])).
% 0.24/0.49  fof(f30,plain,(
% 0.24/0.49    ( ! [X0] : (k2_xboole_0(sK1,X0) = k2_xboole_0(sK1,k2_xboole_0(sK2,X0))) )),
% 0.24/0.49    inference(superposition,[],[f17,f23])).
% 0.24/0.49  fof(f23,plain,(
% 0.24/0.49    sK1 = k2_xboole_0(sK1,sK2)),
% 0.24/0.49    inference(superposition,[],[f19,f15])).
% 0.24/0.49  fof(f19,plain,(
% 0.24/0.49    sK1 = k2_xboole_0(sK2,sK1)),
% 0.24/0.49    inference(resolution,[],[f12,f16])).
% 0.24/0.49  fof(f12,plain,(
% 0.24/0.49    r1_tarski(sK2,sK1)),
% 0.24/0.49    inference(cnf_transformation,[],[f8])).
% 0.24/0.49  fof(f17,plain,(
% 0.24/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.24/0.49    inference(cnf_transformation,[],[f3])).
% 0.24/0.49  fof(f3,axiom,(
% 0.24/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.24/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.24/0.49  % SZS output end Proof for theBenchmark
% 0.24/0.49  % (20627)------------------------------
% 0.24/0.49  % (20627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.24/0.49  % (20627)Termination reason: Refutation
% 0.24/0.49  
% 0.24/0.49  % (20627)Memory used [KB]: 1791
% 0.24/0.49  % (20627)Time elapsed: 0.062 s
% 0.24/0.49  % (20627)------------------------------
% 0.24/0.49  % (20627)------------------------------
% 0.24/0.50  % (20613)Success in time 0.115 s
%------------------------------------------------------------------------------
