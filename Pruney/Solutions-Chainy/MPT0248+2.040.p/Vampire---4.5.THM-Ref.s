%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 188 expanded)
%              Number of leaves         :    8 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 463 expanded)
%              Number of equality atoms :   82 ( 422 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(subsumption_resolution,[],[f90,f88])).

fof(f88,plain,(
    sK1 != k2_tarski(sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK1 != k2_tarski(sK0,sK0) ),
    inference(backward_demodulation,[],[f31,f81])).

fof(f81,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f29,f30,f80,f79])).

fof(f79,plain,
    ( sK2 = k2_tarski(sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,
    ( sK2 = k2_tarski(sK0,sK0)
    | sK2 = k2_tarski(sK0,sK0)
    | sK2 = k2_tarski(sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f37,f46])).

fof(f46,plain,(
    r1_tarski(sK2,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f44,f28])).

fof(f28,plain,(
    k2_tarski(sK0,sK0) = k3_tarski(k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f16,f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f16,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(superposition,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f21,f21])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f23,f18,f18])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f80,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( sK1 = k2_tarski(sK0,sK0)
    | sK1 = k2_tarski(sK0,sK0)
    | sK1 = k2_tarski(sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f37,f43])).

fof(f43,plain,(
    r1_tarski(sK1,k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f32,f28])).

fof(f30,plain,
    ( sK2 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f14,f18])).

fof(f14,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | sK2 != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f15,f18,f18])).

fof(f15,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,
    ( sK1 != k2_tarski(sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f13,f18])).

fof(f13,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f90,plain,(
    sK1 = k2_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f87,f57])).

fof(f57,plain,(
    ! [X1] : k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1 ),
    inference(superposition,[],[f51,f33])).

fof(f51,plain,(
    ! [X4] : k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4 ),
    inference(resolution,[],[f34,f17])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_tarski(X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f87,plain,(
    k2_tarski(sK0,sK0) = k3_tarski(k2_tarski(sK1,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f28,f81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:47:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.43  % (549)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.43  % (541)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.44  % (549)Refutation not found, incomplete strategy% (549)------------------------------
% 0.20/0.44  % (549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (549)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (549)Memory used [KB]: 10746
% 0.20/0.44  % (549)Time elapsed: 0.038 s
% 0.20/0.44  % (549)------------------------------
% 0.20/0.44  % (549)------------------------------
% 0.20/0.44  % (532)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.45  % (533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.45  % (533)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f91,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f90,f88])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    sK1 != k2_tarski(sK0,sK0)),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f84])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | sK1 != k2_tarski(sK0,sK0)),
% 0.20/0.45    inference(backward_demodulation,[],[f31,f81])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    k1_xboole_0 = sK2),
% 0.20/0.45    inference(global_subsumption,[],[f29,f30,f80,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    sK2 = k2_tarski(sK0,sK0) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f78])).
% 0.20/0.46  fof(f78,plain,(
% 0.20/0.46    sK2 = k2_tarski(sK0,sK0) | sK2 = k2_tarski(sK0,sK0) | sK2 = k2_tarski(sK0,sK0) | k1_xboole_0 = sK2),
% 0.20/0.46    inference(resolution,[],[f37,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    r1_tarski(sK2,k2_tarski(sK0,sK0))),
% 0.20/0.46    inference(superposition,[],[f44,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k2_tarski(sK0,sK0) = k3_tarski(k2_tarski(sK1,sK2))),
% 0.20/0.46    inference(definition_unfolding,[],[f16,f18,f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.46    inference(negated_conjecture,[],[f8])).
% 0.20/0.46  fof(f8,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 0.20/0.46    inference(superposition,[],[f32,f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f20,f21,f21])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f19,f21])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f23,f18,f18])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.46  fof(f80,plain,(
% 0.20/0.46    sK1 = k2_tarski(sK0,sK0) | k1_xboole_0 = sK1),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f77])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    sK1 = k2_tarski(sK0,sK0) | sK1 = k2_tarski(sK0,sK0) | sK1 = k2_tarski(sK0,sK0) | k1_xboole_0 = sK1),
% 0.20/0.46    inference(resolution,[],[f37,f43])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    r1_tarski(sK1,k2_tarski(sK0,sK0))),
% 0.20/0.46    inference(superposition,[],[f32,f28])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    sK2 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK1),
% 0.20/0.46    inference(definition_unfolding,[],[f14,f18])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    sK1 != k2_tarski(sK0,sK0) | sK2 != k2_tarski(sK0,sK0)),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f18,f18])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    sK1 != k2_tarski(sK0,sK0) | k1_xboole_0 != sK2),
% 0.20/0.46    inference(definition_unfolding,[],[f13,f18])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    sK1 = k2_tarski(sK0,sK0)),
% 0.20/0.46    inference(forward_demodulation,[],[f87,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X1] : (k3_tarski(k2_tarski(X1,k1_xboole_0)) = X1) )),
% 0.20/0.46    inference(superposition,[],[f51,f33])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X4] : (k3_tarski(k2_tarski(k1_xboole_0,X4)) = X4) )),
% 0.20/0.46    inference(resolution,[],[f34,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1) )),
% 0.20/0.46    inference(definition_unfolding,[],[f22,f21])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    k2_tarski(sK0,sK0) = k3_tarski(k2_tarski(sK1,k1_xboole_0))),
% 0.20/0.46    inference(backward_demodulation,[],[f28,f81])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (533)------------------------------
% 0.20/0.46  % (533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (533)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (533)Memory used [KB]: 6268
% 0.20/0.46  % (533)Time elapsed: 0.052 s
% 0.20/0.46  % (533)------------------------------
% 0.20/0.46  % (533)------------------------------
% 0.20/0.46  % (523)Success in time 0.116 s
%------------------------------------------------------------------------------
