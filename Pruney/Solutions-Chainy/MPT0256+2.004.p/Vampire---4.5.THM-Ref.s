%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:59 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   43 (  75 expanded)
%              Number of leaves         :   10 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 114 expanded)
%              Number of equality atoms :   18 (  48 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(resolution,[],[f105,f49])).

fof(f49,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(resolution,[],[f42,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f30,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f105,plain,(
    ! [X6] : ~ r2_hidden(X6,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f104,f18])).

fof(f18,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f104,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k2_enumset1(sK1,sK1,sK1,sK1))
      | r2_hidden(sK1,sK0) ) ),
    inference(superposition,[],[f94,f35])).

fof(f35,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f17,f34,f22,f34])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f33])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f17,plain,(
    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))))
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f46,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f22,f22])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f34])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:23:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.29/0.55  % (12242)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.55  % (12259)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.55  % (12250)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.53/0.56  % (12244)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.53/0.56  % (12242)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % (12252)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (12243)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.53/0.56  % (12251)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.53/0.57  % (12260)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f108,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(resolution,[],[f105,f49])).
% 1.53/0.57  fof(f49,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X1))) )),
% 1.53/0.57    inference(resolution,[],[f42,f44])).
% 1.53/0.57  fof(f44,plain,(
% 1.53/0.57    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.53/0.57    inference(duplicate_literal_removal,[],[f43])).
% 1.53/0.57  fof(f43,plain,(
% 1.53/0.57    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.53/0.57    inference(resolution,[],[f28,f27])).
% 1.53/0.57  fof(f27,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f16,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f16])).
% 1.53/0.57  fof(f42,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f30,f33])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f21,f29])).
% 1.53/0.57  fof(f29,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,axiom,(
% 1.53/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.53/0.57  fof(f30,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,axiom,(
% 1.53/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.53/0.57  fof(f105,plain,(
% 1.53/0.57    ( ! [X6] : (~r2_hidden(X6,k2_enumset1(sK1,sK1,sK1,sK1))) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f104,f18])).
% 1.53/0.57  fof(f18,plain,(
% 1.53/0.57    ~r2_hidden(sK1,sK0)),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.53/0.57    inference(negated_conjecture,[],[f10])).
% 1.53/0.57  fof(f10,conjecture,(
% 1.53/0.57    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 1.53/0.57  fof(f104,plain,(
% 1.53/0.57    ( ! [X6] : (~r2_hidden(X6,k2_enumset1(sK1,sK1,sK1,sK1)) | r2_hidden(sK1,sK0)) )),
% 1.53/0.57    inference(superposition,[],[f94,f35])).
% 1.53/0.57  fof(f35,plain,(
% 1.53/0.57    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.53/0.57    inference(definition_unfolding,[],[f17,f34,f22,f34])).
% 1.53/0.57  fof(f22,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.53/0.57    inference(cnf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.53/0.57  fof(f34,plain,(
% 1.53/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f19,f33])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f5])).
% 1.53/0.57  fof(f5,axiom,(
% 1.53/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.53/0.57  fof(f17,plain,(
% 1.53/0.57    k1_tarski(sK1) = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.53/0.57    inference(cnf_transformation,[],[f13])).
% 1.53/0.57  fof(f94,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k4_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) | r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(superposition,[],[f46,f36])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.53/0.57    inference(definition_unfolding,[],[f20,f22,f22])).
% 1.53/0.57  fof(f20,plain,(
% 1.53/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.57  fof(f46,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k4_xboole_0(k2_enumset1(X0,X0,X0,X0),X1))) | r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(resolution,[],[f39,f38])).
% 1.53/0.57  fof(f38,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.53/0.57    inference(definition_unfolding,[],[f23,f22])).
% 1.53/0.57  fof(f23,plain,(
% 1.53/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.53/0.57    inference(ennf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.57    inference(rectify,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.53/0.57    inference(definition_unfolding,[],[f25,f34])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f15])).
% 1.53/0.57  fof(f15,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,axiom,(
% 1.53/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (12242)------------------------------
% 1.53/0.57  % (12242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (12242)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (12242)Memory used [KB]: 6268
% 1.53/0.57  % (12242)Time elapsed: 0.130 s
% 1.53/0.57  % (12242)------------------------------
% 1.53/0.57  % (12242)------------------------------
% 1.53/0.57  % (12235)Success in time 0.207 s
%------------------------------------------------------------------------------
