%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:50 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   39 (  62 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  84 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,(
    sK0 != sK0 ),
    inference(superposition,[],[f38,f42])).

fof(f42,plain,(
    ! [X0] : k6_subset_1(X0,k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f40,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK1(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(resolution,[],[f34,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f24,f19,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f38,plain,(
    sK0 != k6_subset_1(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f31,f32])).

fof(f32,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k6_subset_1(k2_xboole_0(X0,X1),X1) ),
    inference(definition_unfolding,[],[f21,f19,f19])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f31,plain,(
    sK0 != k6_subset_1(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(definition_unfolding,[],[f16,f30,f29])).

% (31929)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f30,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f18,f29])).

fof(f18,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f16,plain,(
    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:36:12 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.44  % (31914)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.18/0.46  % (31914)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f46,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f43])).
% 0.18/0.46  fof(f43,plain,(
% 0.18/0.46    sK0 != sK0),
% 0.18/0.46    inference(superposition,[],[f38,f42])).
% 0.18/0.46  fof(f42,plain,(
% 0.18/0.46    ( ! [X0] : (k6_subset_1(X0,k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.18/0.46    inference(resolution,[],[f40,f37])).
% 0.18/0.46  fof(f37,plain,(
% 0.18/0.46    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.18/0.46    inference(duplicate_literal_removal,[],[f36])).
% 0.18/0.46  fof(f36,plain,(
% 0.18/0.46    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.18/0.46    inference(resolution,[],[f23,f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f14])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.18/0.46    inference(unused_predicate_definition_removal,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r2_hidden(sK1(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f14])).
% 0.18/0.46  fof(f40,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 0.18/0.46    inference(resolution,[],[f34,f26])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f9])).
% 0.18/0.46  fof(f9,axiom,(
% 0.18/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(X1,X0) | k6_subset_1(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 0.18/0.46    inference(definition_unfolding,[],[f24,f19,f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f17,f28])).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f20,f27])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,axiom,(
% 0.18/0.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.18/0.46  fof(f38,plain,(
% 0.18/0.46    sK0 != k6_subset_1(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.18/0.46    inference(superposition,[],[f31,f32])).
% 0.18/0.46  fof(f32,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k6_subset_1(k2_xboole_0(X0,X1),X1)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f21,f19,f19])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    sK0 != k6_subset_1(k2_xboole_0(sK0,k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.18/0.46    inference(definition_unfolding,[],[f16,f30,f29])).
% 0.18/0.46  % (31929)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.18/0.46    inference(definition_unfolding,[],[f18,f29])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,axiom,(
% 0.18/0.46    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    sK0 != k6_subset_1(k1_ordinal1(sK0),k1_tarski(sK0))),
% 0.18/0.46    inference(cnf_transformation,[],[f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0),
% 0.18/0.46    inference(ennf_transformation,[],[f11])).
% 0.18/0.46  fof(f11,negated_conjecture,(
% 0.18/0.46    ~! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.18/0.46    inference(negated_conjecture,[],[f10])).
% 0.18/0.46  fof(f10,conjecture,(
% 0.18/0.46    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 0.18/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_ordinal1)).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (31914)------------------------------
% 0.18/0.46  % (31914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (31914)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (31914)Memory used [KB]: 6140
% 0.18/0.46  % (31914)Time elapsed: 0.086 s
% 0.18/0.46  % (31914)------------------------------
% 0.18/0.46  % (31914)------------------------------
% 0.18/0.47  % (31907)Success in time 0.123 s
%------------------------------------------------------------------------------
