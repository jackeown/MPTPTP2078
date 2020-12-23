%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  45 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  63 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f63,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f25,f59,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f59,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f51,f55,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f36,f40])).

fof(f40,plain,(
    k1_xboole_0 = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    inference(definition_unfolding,[],[f19,f39])).

fof(f19,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f51,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f25,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n002.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 16:56:22 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.19/0.44  % (10846)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.45  % (10846)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.45  % SZS output start Proof for theBenchmark
% 0.19/0.45  fof(f63,plain,(
% 0.19/0.45    $false),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f25,f59,f41])).
% 0.19/0.45  fof(f41,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f22,f39])).
% 0.19/0.45  fof(f39,plain,(
% 0.19/0.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f23,f38])).
% 0.19/0.45  fof(f38,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.45    inference(definition_unfolding,[],[f35,f37])).
% 0.19/0.45  fof(f37,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f10])).
% 0.19/0.45  fof(f10,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.45  fof(f35,plain,(
% 0.19/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f9])).
% 0.19/0.45  fof(f9,axiom,(
% 0.19/0.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.45  fof(f23,plain,(
% 0.19/0.45    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f8])).
% 0.19/0.45  fof(f8,axiom,(
% 0.19/0.45    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.45  fof(f22,plain,(
% 0.19/0.45    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f16])).
% 0.19/0.45  fof(f16,plain,(
% 0.19/0.45    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.45    inference(ennf_transformation,[],[f11])).
% 0.19/0.45  fof(f11,axiom,(
% 0.19/0.45    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.19/0.45  fof(f59,plain,(
% 0.19/0.45    r2_hidden(sK0,k1_xboole_0)),
% 0.19/0.45    inference(unit_resulting_resolution,[],[f51,f55,f32])).
% 0.19/0.45  fof(f32,plain,(
% 0.19/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f18])).
% 0.19/0.45  fof(f18,plain,(
% 0.19/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.45    inference(ennf_transformation,[],[f2])).
% 0.19/0.45  fof(f2,axiom,(
% 0.19/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.45  fof(f55,plain,(
% 0.19/0.45    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)),
% 0.19/0.45    inference(superposition,[],[f36,f40])).
% 0.19/0.45  fof(f40,plain,(
% 0.19/0.45    k1_xboole_0 = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.19/0.45    inference(definition_unfolding,[],[f19,f39])).
% 0.19/0.45  fof(f19,plain,(
% 0.19/0.45    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.19/0.45    inference(cnf_transformation,[],[f15])).
% 0.19/0.45  fof(f15,plain,(
% 0.19/0.45    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.45    inference(ennf_transformation,[],[f14])).
% 0.19/0.45  fof(f14,negated_conjecture,(
% 0.19/0.45    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.45    inference(negated_conjecture,[],[f13])).
% 0.19/0.45  fof(f13,conjecture,(
% 0.19/0.45    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.19/0.45  fof(f36,plain,(
% 0.19/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.45    inference(cnf_transformation,[],[f6])).
% 0.19/0.45  fof(f6,axiom,(
% 0.19/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.45  fof(f51,plain,(
% 0.19/0.45    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 0.19/0.45    inference(equality_resolution,[],[f50])).
% 0.19/0.45  fof(f50,plain,(
% 0.19/0.45    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 0.19/0.45    inference(equality_resolution,[],[f43])).
% 0.19/0.45  fof(f43,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.19/0.45    inference(definition_unfolding,[],[f30,f38])).
% 0.19/0.45  fof(f30,plain,(
% 0.19/0.45    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.19/0.45    inference(cnf_transformation,[],[f7])).
% 0.19/0.45  fof(f7,axiom,(
% 0.19/0.45    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.19/0.45  fof(f25,plain,(
% 0.19/0.45    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.19/0.45    inference(cnf_transformation,[],[f5])).
% 0.19/0.45  fof(f5,axiom,(
% 0.19/0.45    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.19/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.19/0.45  % SZS output end Proof for theBenchmark
% 0.19/0.45  % (10846)------------------------------
% 0.19/0.45  % (10846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (10846)Termination reason: Refutation
% 0.19/0.45  
% 0.19/0.45  % (10846)Memory used [KB]: 6140
% 0.19/0.45  % (10846)Time elapsed: 0.085 s
% 0.19/0.45  % (10846)------------------------------
% 0.19/0.45  % (10846)------------------------------
% 0.19/0.45  % (10839)Success in time 0.116 s
%------------------------------------------------------------------------------
