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
% DateTime   : Thu Dec  3 12:41:35 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 194 expanded)
%              Number of leaves         :   16 (  63 expanded)
%              Depth                    :   17
%              Number of atoms          :  104 ( 243 expanded)
%              Number of equality atoms :   27 ( 148 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f163,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f52,f157,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))
      | ~ r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f87,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
      | ~ r1_tarski(X2,X1) ) ),
    inference(superposition,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f47,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f157,plain,(
    ~ r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) ),
    inference(resolution,[],[f156,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f156,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f155,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X0),X2)
      | ~ r1_tarski(X0,X2) ) ),
    inference(superposition,[],[f40,f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f155,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))
    | ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(resolution,[],[f154,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f154,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f153,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f88,f29])).

fof(f88,plain,(
    ! [X4,X3] : r1_tarski(X3,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3)))) ),
    inference(superposition,[],[f49,f50])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f153,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))
    | ~ r1_tarski(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) ),
    inference(resolution,[],[f78,f34])).

fof(f78,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))
    | ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f56,f29])).

fof(f56,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f55,f50])).

fof(f55,plain,(
    ~ r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f54,f29])).

fof(f54,plain,(
    ~ r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f48,f50])).

fof(f48,plain,(
    ~ r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(definition_unfolding,[],[f27,f47,f47])).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:55:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.43  % (25293)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.44  % (25312)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.45  % (25304)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.45  % (25304)Refutation not found, incomplete strategy% (25304)------------------------------
% 0.19/0.45  % (25304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (25304)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (25304)Memory used [KB]: 1663
% 0.19/0.46  % (25304)Time elapsed: 0.078 s
% 0.19/0.46  % (25304)------------------------------
% 0.19/0.46  % (25304)------------------------------
% 0.19/0.47  % (25312)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f163,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(unit_resulting_resolution,[],[f52,f157,f101])).
% 0.19/0.47  fof(f101,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(X2,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) | ~r1_tarski(X2,X0)) )),
% 0.19/0.47    inference(superposition,[],[f87,f29])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.47  fof(f87,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) | ~r1_tarski(X2,X1)) )),
% 0.19/0.47    inference(superposition,[],[f51,f50])).
% 0.19/0.47  fof(f50,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.19/0.47    inference(definition_unfolding,[],[f33,f47,f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.19/0.47  fof(f47,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.19/0.47    inference(definition_unfolding,[],[f30,f46])).
% 0.19/0.47  fof(f46,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f31,f45])).
% 0.19/0.47  fof(f45,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f38,f44])).
% 0.19/0.47  fof(f44,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f42,f43])).
% 0.19/0.47  fof(f43,plain,(
% 0.19/0.47    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f12])).
% 0.19/0.47  fof(f12,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,axiom,(
% 0.19/0.47    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.19/0.47  fof(f38,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f10])).
% 0.19/0.47  fof(f10,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,axiom,(
% 0.19/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f13])).
% 0.19/0.47  fof(f13,axiom,(
% 0.19/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,axiom,(
% 0.19/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.19/0.47  fof(f51,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(definition_unfolding,[],[f39,f47])).
% 0.19/0.47  fof(f39,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f19])).
% 0.19/0.47  fof(f19,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.19/0.47  fof(f157,plain,(
% 0.19/0.47    ~r1_tarski(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),
% 0.19/0.47    inference(resolution,[],[f156,f34])).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f18])).
% 0.19/0.47  fof(f18,plain,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f14])).
% 0.19/0.47  fof(f14,axiom,(
% 0.19/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 0.19/0.47  fof(f156,plain,(
% 0.19/0.47    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(subsumption_resolution,[],[f155,f58])).
% 0.19/0.47  fof(f58,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X2) | ~r1_tarski(X0,X2)) )),
% 0.19/0.47    inference(superposition,[],[f40,f29])).
% 0.19/0.47  fof(f40,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f20])).
% 0.19/0.47  fof(f20,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(ennf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.19/0.47  fof(f155,plain,(
% 0.19/0.47    ~r1_tarski(k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) | ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(resolution,[],[f154,f41])).
% 0.19/0.47  fof(f41,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.19/0.47    inference(flattening,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f6])).
% 0.19/0.47  fof(f6,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.19/0.47  fof(f154,plain,(
% 0.19/0.47    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(subsumption_resolution,[],[f153,f92])).
% 0.19/0.47  fof(f92,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 0.19/0.47    inference(superposition,[],[f88,f29])).
% 0.19/0.47  fof(f88,plain,(
% 0.19/0.47    ( ! [X4,X3] : (r1_tarski(X3,k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))))) )),
% 0.19/0.47    inference(superposition,[],[f49,f50])).
% 0.19/0.47  fof(f49,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 0.19/0.47    inference(definition_unfolding,[],[f28,f47])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,axiom,(
% 0.19/0.47    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.47  fof(f153,plain,(
% 0.19/0.47    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) | ~r1_tarski(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),
% 0.19/0.47    inference(resolution,[],[f78,f34])).
% 0.19/0.47  fof(f78,plain,(
% 0.19/0.47    ~r1_tarski(k1_zfmisc_1(sK0),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) | ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(resolution,[],[f57,f41])).
% 0.19/0.47  fof(f57,plain,(
% 0.19/0.47    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(forward_demodulation,[],[f56,f29])).
% 0.19/0.47  fof(f56,plain,(
% 0.19/0.47    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k5_xboole_0(k1_zfmisc_1(sK1),k3_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(forward_demodulation,[],[f55,f50])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ~r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 0.19/0.47    inference(forward_demodulation,[],[f54,f29])).
% 0.19/0.47  fof(f54,plain,(
% 0.19/0.47    ~r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 0.19/0.47    inference(backward_demodulation,[],[f48,f50])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    ~r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 0.19/0.47    inference(definition_unfolding,[],[f27,f47,f47])).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.19/0.47    inference(cnf_transformation,[],[f24])).
% 0.19/0.47  fof(f24,plain,(
% 0.19/0.47    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 0.19/0.47    introduced(choice_axiom,[])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.19/0.47    inference(ennf_transformation,[],[f16])).
% 0.19/0.47  fof(f16,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.19/0.47    inference(negated_conjecture,[],[f15])).
% 0.19/0.47  fof(f15,conjecture,(
% 0.19/0.47    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.47    inference(equality_resolution,[],[f36])).
% 0.19/0.47  fof(f36,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.47    inference(flattening,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.47    inference(nnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (25312)------------------------------
% 0.19/0.47  % (25312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (25312)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (25312)Memory used [KB]: 6396
% 0.19/0.47  % (25312)Time elapsed: 0.080 s
% 0.19/0.47  % (25312)------------------------------
% 0.19/0.47  % (25312)------------------------------
% 0.19/0.47  % (25287)Success in time 0.127 s
%------------------------------------------------------------------------------
