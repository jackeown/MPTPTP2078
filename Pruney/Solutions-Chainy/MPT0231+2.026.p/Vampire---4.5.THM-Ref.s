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
% DateTime   : Thu Dec  3 12:36:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  50 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 (  87 expanded)
%              Number of equality atoms :   32 (  53 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f12])).

fof(f12,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f45,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f21,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f43,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK1))
      | sK2 = X4 ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X4] :
      ( sK2 = X4
      | sK2 = X4
      | ~ r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK1)) ) ),
    inference(resolution,[],[f36,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
      | ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) ) ),
    inference(resolution,[],[f15,f25])).

fof(f25,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f11,f23,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f13,f23])).

fof(f13,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (24675)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (24675)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f45,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    sK0 != sK2),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    sK0 = sK2),
% 0.20/0.49    inference(resolution,[],[f43,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.20/0.49    inference(equality_resolution,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f14,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X4] : (~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK1)) | sK2 = X4) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X4] : (sK2 = X4 | sK2 = X4 | ~r2_hidden(X4,k2_enumset1(sK0,sK0,sK0,sK1))) )),
% 0.20/0.49    inference(resolution,[],[f36,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) | ~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))) )),
% 0.20/0.49    inference(resolution,[],[f15,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK2))),
% 0.20/0.49    inference(definition_unfolding,[],[f11,f23,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f13,f23])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.20/0.49    inference(equality_resolution,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.49    inference(definition_unfolding,[],[f20,f23])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (24675)------------------------------
% 0.20/0.49  % (24675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24675)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (24675)Memory used [KB]: 6140
% 0.20/0.49  % (24675)Time elapsed: 0.107 s
% 0.20/0.49  % (24675)------------------------------
% 0.20/0.49  % (24675)------------------------------
% 0.20/0.50  % (24668)Success in time 0.14 s
%------------------------------------------------------------------------------
