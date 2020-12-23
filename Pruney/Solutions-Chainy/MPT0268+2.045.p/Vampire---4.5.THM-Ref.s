%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 218 expanded)
%              Number of leaves         :   10 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 324 expanded)
%              Number of equality atoms :   27 ( 178 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f183,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f129,f149,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f149,plain,(
    ! [X0] : ~ r2_hidden(sK2(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0),k5_xboole_0(sK0,k3_xboole_0(sK0,X0))) ),
    inference(unit_resulting_resolution,[],[f147,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f33,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f147,plain,(
    ! [X0] : ~ sP4(sK2(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0),X0,sK0) ),
    inference(unit_resulting_resolution,[],[f140,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f140,plain,(
    ~ r2_hidden(sK2(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f129,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f129,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f79,f107,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f107,plain,(
    r1_tarski(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))) ),
    inference(unit_resulting_resolution,[],[f51,f78,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f20,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f18,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X0)
      | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

fof(f78,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f55,f42])).

fof(f42,plain,
    ( sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ r2_hidden(sK1,sK0) ),
    inference(definition_unfolding,[],[f16,f20,f40])).

fof(f16,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f37,f20,f40])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f79,plain,(
    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f78,f41])).

fof(f41,plain,
    ( sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))
    | r2_hidden(sK1,sK0) ),
    inference(definition_unfolding,[],[f17,f20,f40])).

fof(f17,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (7737)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (7745)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (7745)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (7727)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (7728)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.54  % (7729)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.54  % SZS output start Proof for theBenchmark
% 1.24/0.54  fof(f183,plain,(
% 1.24/0.54    $false),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f129,f149,f25])).
% 1.24/0.54  fof(f25,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f13])).
% 1.24/0.54  fof(f13,plain,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.24/0.54    inference(ennf_transformation,[],[f1])).
% 1.24/0.54  fof(f1,axiom,(
% 1.24/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.24/0.54  fof(f149,plain,(
% 1.24/0.54    ( ! [X0] : (~r2_hidden(sK2(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0),k5_xboole_0(sK0,k3_xboole_0(sK0,X0)))) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f147,f53])).
% 1.24/0.54  fof(f53,plain,(
% 1.24/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | sP4(X3,X1,X0)) )),
% 1.24/0.54    inference(equality_resolution,[],[f46])).
% 1.24/0.54  fof(f46,plain,(
% 1.24/0.54    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.24/0.54    inference(definition_unfolding,[],[f33,f20])).
% 1.24/0.54  fof(f20,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f4])).
% 1.24/0.54  fof(f4,axiom,(
% 1.24/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.24/0.54  fof(f33,plain,(
% 1.24/0.54    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/0.54    inference(cnf_transformation,[],[f2])).
% 1.24/0.54  fof(f2,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.24/0.54  fof(f147,plain,(
% 1.24/0.54    ( ! [X0] : (~sP4(sK2(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0),X0,sK0)) )),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f140,f30])).
% 1.24/0.54  fof(f30,plain,(
% 1.24/0.54    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f2])).
% 1.24/0.54  fof(f140,plain,(
% 1.24/0.54    ~r2_hidden(sK2(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0),sK0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f129,f26])).
% 1.24/0.54  fof(f26,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f13])).
% 1.24/0.54  fof(f129,plain,(
% 1.24/0.54    ~r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),sK0)),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f79,f107,f23])).
% 1.24/0.54  fof(f23,plain,(
% 1.24/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.24/0.54    inference(cnf_transformation,[],[f3])).
% 1.24/0.54  fof(f3,axiom,(
% 1.24/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.24/0.54  fof(f107,plain,(
% 1.24/0.54    r1_tarski(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))))),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f51,f78,f43])).
% 1.24/0.54  fof(f43,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.24/0.54    inference(definition_unfolding,[],[f28,f20,f40])).
% 1.24/0.54  fof(f40,plain,(
% 1.24/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.24/0.54    inference(definition_unfolding,[],[f18,f39])).
% 1.24/0.54  fof(f39,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.24/0.54    inference(definition_unfolding,[],[f19,f27])).
% 1.24/0.54  fof(f27,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f7])).
% 1.24/0.54  fof(f7,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.24/0.54  fof(f19,plain,(
% 1.24/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f6])).
% 1.24/0.54  fof(f6,axiom,(
% 1.24/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.24/0.54  fof(f18,plain,(
% 1.24/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.24/0.54    inference(cnf_transformation,[],[f5])).
% 1.24/0.54  fof(f5,axiom,(
% 1.24/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.24/0.54  fof(f28,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X0) | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f15])).
% 1.24/0.54  fof(f15,plain,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1))),
% 1.24/0.54    inference(flattening,[],[f14])).
% 1.24/0.54  fof(f14,plain,(
% 1.24/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.24/0.54    inference(ennf_transformation,[],[f8])).
% 1.24/0.54  fof(f8,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).
% 1.24/0.54  fof(f78,plain,(
% 1.24/0.54    ~r2_hidden(sK1,sK0)),
% 1.24/0.54    inference(duplicate_literal_removal,[],[f77])).
% 1.24/0.54  fof(f77,plain,(
% 1.24/0.54    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,sK0)),
% 1.24/0.54    inference(superposition,[],[f55,f42])).
% 1.24/0.54  fof(f42,plain,(
% 1.24/0.54    sK0 = k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | ~r2_hidden(sK1,sK0)),
% 1.24/0.54    inference(definition_unfolding,[],[f16,f20,f40])).
% 1.24/0.54  fof(f16,plain,(
% 1.24/0.54    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.24/0.54    inference(cnf_transformation,[],[f12])).
% 1.24/0.54  fof(f12,plain,(
% 1.24/0.54    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.24/0.54    inference(ennf_transformation,[],[f11])).
% 1.24/0.54  fof(f11,negated_conjecture,(
% 1.24/0.54    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.24/0.54    inference(negated_conjecture,[],[f10])).
% 1.24/0.54  fof(f10,conjecture,(
% 1.24/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.24/0.54  fof(f55,plain,(
% 1.24/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 1.24/0.54    inference(equality_resolution,[],[f49])).
% 1.24/0.54  fof(f49,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 1.24/0.54    inference(definition_unfolding,[],[f37,f20,f40])).
% 1.24/0.54  fof(f37,plain,(
% 1.24/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.24/0.54    inference(cnf_transformation,[],[f9])).
% 1.24/0.54  fof(f9,axiom,(
% 1.24/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.24/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.24/0.54  fof(f51,plain,(
% 1.24/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.24/0.54    inference(equality_resolution,[],[f22])).
% 1.24/0.54  fof(f22,plain,(
% 1.24/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.24/0.54    inference(cnf_transformation,[],[f3])).
% 1.24/0.54  fof(f79,plain,(
% 1.24/0.54    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 1.24/0.54    inference(unit_resulting_resolution,[],[f78,f41])).
% 1.24/0.54  fof(f41,plain,(
% 1.24/0.54    sK0 != k5_xboole_0(sK0,k3_xboole_0(sK0,k2_enumset1(sK1,sK1,sK1,sK1))) | r2_hidden(sK1,sK0)),
% 1.24/0.54    inference(definition_unfolding,[],[f17,f20,f40])).
% 1.24/0.54  fof(f17,plain,(
% 1.24/0.54    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.24/0.54    inference(cnf_transformation,[],[f12])).
% 1.24/0.54  % SZS output end Proof for theBenchmark
% 1.24/0.54  % (7745)------------------------------
% 1.24/0.54  % (7745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (7745)Termination reason: Refutation
% 1.24/0.54  
% 1.24/0.54  % (7745)Memory used [KB]: 6268
% 1.24/0.54  % (7745)Time elapsed: 0.104 s
% 1.24/0.54  % (7745)------------------------------
% 1.24/0.54  % (7745)------------------------------
% 1.24/0.55  % (7720)Success in time 0.17 s
%------------------------------------------------------------------------------
