%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   34 (  53 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 101 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f45,f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k9_relat_1(sK2,k2_xboole_0(X0,X1)))
      | r1_tarski(k4_xboole_0(X2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,k4_xboole_0(X1,X0))) ) ),
    inference(superposition,[],[f37,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k9_relat_1(sK2,k2_xboole_0(X0,X1)))
      | r1_tarski(k4_xboole_0(X2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,X1)) ) ),
    inference(superposition,[],[f25,f36])).

fof(f36,plain,(
    ! [X0,X1] : k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f30,plain,(
    ~ r1_tarski(k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f29,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f29,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f18,f19])).

fof(f18,plain,(
    ~ r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X3] : r1_tarski(k9_relat_1(sK2,X3),k9_relat_1(sK2,k2_xboole_0(X2,X3))) ),
    inference(superposition,[],[f35,f36])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f34,f20])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (26168)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.47  % (26156)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.48  % (26148)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.50  % (26148)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f157,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f45,f30,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,k9_relat_1(sK2,k2_xboole_0(X0,X1))) | r1_tarski(k4_xboole_0(X2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,k4_xboole_0(X1,X0)))) )),
% 0.20/0.50    inference(superposition,[],[f37,f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,k9_relat_1(sK2,k2_xboole_0(X0,X1))) | r1_tarski(k4_xboole_0(X2,k9_relat_1(sK2,X0)),k9_relat_1(sK2,X1))) )),
% 0.20/0.50    inference(superposition,[],[f25,f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k9_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1))) )),
% 0.20/0.50    inference(resolution,[],[f24,f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    v1_relat_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)),k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_relat_1)).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k9_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ~r1_tarski(k4_xboole_0(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 0.20/0.50    inference(forward_demodulation,[],[f29,f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k4_xboole_0(sK0,sK1)))),
% 0.20/0.50    inference(forward_demodulation,[],[f18,f19])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ~r1_tarski(k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 0.20/0.50    inference(cnf_transformation,[],[f14])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK2,X3),k9_relat_1(sK2,k2_xboole_0(X2,X3)))) )),
% 0.20/0.50    inference(superposition,[],[f35,f36])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f34,f20])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) )),
% 0.20/0.50    inference(resolution,[],[f26,f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.50    inference(equality_resolution,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (26148)------------------------------
% 0.20/0.50  % (26148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (26148)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (26148)Memory used [KB]: 1918
% 0.20/0.50  % (26148)Time elapsed: 0.074 s
% 0.20/0.50  % (26148)------------------------------
% 0.20/0.50  % (26148)------------------------------
% 0.20/0.50  % (26136)Success in time 0.148 s
%------------------------------------------------------------------------------
