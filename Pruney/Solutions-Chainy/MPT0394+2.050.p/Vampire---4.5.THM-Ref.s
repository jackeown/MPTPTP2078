%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 268 expanded)
%              Number of leaves         :   15 (  81 expanded)
%              Depth                    :   18
%              Number of atoms          :  126 ( 526 expanded)
%              Number of equality atoms :   71 ( 215 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f49,f179])).

fof(f179,plain,(
    ! [X8,X7] : k1_setfam_1(k1_enumset1(X7,X7,X8)) = k4_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f178,f51])).

fof(f51,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f26,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f178,plain,(
    ! [X8,X7] : k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),X8)) = k1_setfam_1(k1_enumset1(X7,X7,X8)) ),
    inference(forward_demodulation,[],[f177,f175])).

fof(f175,plain,(
    ! [X8,X7] : k1_enumset1(X7,X7,X8) = k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8))) ),
    inference(forward_demodulation,[],[f168,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(definition_unfolding,[],[f41,f44,f45])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f30,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f168,plain,(
    ! [X8,X7] : k3_tarski(k1_enumset1(k1_enumset1(X7,X7,X7),k1_enumset1(X7,X7,X7),k1_enumset1(X7,X7,X8))) = k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8))) ),
    inference(superposition,[],[f54,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3))) ),
    inference(definition_unfolding,[],[f42,f46,f44,f45])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f177,plain,(
    ! [X8,X7] : k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),X8)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8)))) ),
    inference(subsumption_resolution,[],[f172,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(backward_demodulation,[],[f65,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f50,f81])).

fof(f81,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(resolution,[],[f76,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f76,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(resolution,[],[f72,f68])).

fof(f68,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f63,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f33,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f63,f34])).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f65,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0)) ),
    inference(resolution,[],[f56,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X1] : ~ r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1)) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f39,f45,f45])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

fof(f172,plain,(
    ! [X8,X7] :
      ( k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),X8)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8))))
      | k1_xboole_0 = k1_enumset1(X7,X7,X7) ) ),
    inference(superposition,[],[f132,f54])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0)))) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X0))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f127,f84])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0)))) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X0))
      | k1_xboole_0 = k1_enumset1(X0,X0,X0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f52,f51])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f44,f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f49,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1)) ),
    inference(definition_unfolding,[],[f24,f32,f31])).

fof(f24,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:05:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (23669)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (23662)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (23662)Refutation not found, incomplete strategy% (23662)------------------------------
% 0.21/0.52  % (23662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23652)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (23662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23662)Memory used [KB]: 6140
% 0.21/0.52  % (23662)Time elapsed: 0.005 s
% 0.21/0.52  % (23662)------------------------------
% 0.21/0.52  % (23662)------------------------------
% 0.21/0.52  % (23669)Refutation not found, incomplete strategy% (23669)------------------------------
% 0.21/0.52  % (23669)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23669)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23669)Memory used [KB]: 10618
% 0.21/0.52  % (23669)Time elapsed: 0.069 s
% 0.21/0.52  % (23669)------------------------------
% 0.21/0.52  % (23669)------------------------------
% 0.21/0.53  % (23652)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f185])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.53    inference(superposition,[],[f49,f179])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k1_setfam_1(k1_enumset1(X7,X7,X8)) = k4_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f178,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f26,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f27,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,axiom,(
% 0.21/0.53    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),X8)) = k1_setfam_1(k1_enumset1(X7,X7,X8))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f177,f175])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k1_enumset1(X7,X7,X8) = k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8)))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f168,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f40,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f41,f44,f45])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f30,f31])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k3_tarski(k1_enumset1(k1_enumset1(X7,X7,X7),k1_enumset1(X7,X7,X7),k1_enumset1(X7,X7,X8))) = k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8)))) )),
% 0.21/0.53    inference(superposition,[],[f54,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k1_enumset1(X3,X3,X3)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f42,f46,f44,f45])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),X8)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8))))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f172,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f65,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(backward_demodulation,[],[f50,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 0.21/0.53    inference(resolution,[],[f76,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.53    inference(resolution,[],[f72,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.21/0.53    inference(resolution,[],[f63,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f33,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f69,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    inference(equality_resolution,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(resolution,[],[f63,f34])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f25,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0))) )),
% 0.21/0.53    inference(resolution,[],[f56,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X1] : (~r1_xboole_0(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)) | X0 != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f39,f45,f45])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),k4_xboole_0(k1_setfam_1(k1_enumset1(X7,X7,X7)),X8)) = k1_setfam_1(k3_tarski(k1_enumset1(k1_enumset1(X7,X8,X8),k1_enumset1(X7,X8,X8),k1_enumset1(X8,X8,X8)))) | k1_xboole_0 = k1_enumset1(X7,X7,X7)) )),
% 0.21/0.53    inference(superposition,[],[f132,f54])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0)))) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X0)) | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f84])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X1,X1,k1_enumset1(X0,X0,X0)))) = k4_xboole_0(k1_setfam_1(X1),k4_xboole_0(k1_setfam_1(X1),X0)) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | k1_xboole_0 = X1) )),
% 0.21/0.53    inference(superposition,[],[f52,f51])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_setfam_1(k3_tarski(k1_enumset1(X0,X0,X1))) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(definition_unfolding,[],[f38,f44,f32])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k1_enumset1(sK0,sK0,sK1))),
% 0.21/0.53    inference(definition_unfolding,[],[f24,f32,f31])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (23652)------------------------------
% 0.21/0.53  % (23652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23652)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (23652)Memory used [KB]: 6268
% 0.21/0.53  % (23652)Time elapsed: 0.078 s
% 0.21/0.53  % (23652)------------------------------
% 0.21/0.53  % (23652)------------------------------
% 0.21/0.53  % (23645)Success in time 0.164 s
%------------------------------------------------------------------------------
