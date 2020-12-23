%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 615 expanded)
%              Number of leaves         :   18 ( 210 expanded)
%              Depth                    :   17
%              Number of atoms          :  218 ( 787 expanded)
%              Number of equality atoms :  167 ( 736 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f186,plain,(
    $false ),
    inference(subsumption_resolution,[],[f185,f127])).

fof(f127,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f113,f118])).

fof(f118,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) ),
    inference(superposition,[],[f117,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f117,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) ),
    inference(forward_demodulation,[],[f116,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2) ),
    inference(definition_unfolding,[],[f48,f65,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).

fof(f116,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f114,f75])).

fof(f114,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) ),
    inference(superposition,[],[f69,f70])).

fof(f70,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f33,f41,f68,f68])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

% (12008)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (12006)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (12015)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (12006)Refutation not found, incomplete strategy% (12006)------------------------------
% (12006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12006)Termination reason: Refutation not found, incomplete strategy

% (12006)Memory used [KB]: 1663
% (12006)Time elapsed: 0.145 s
% (12006)------------------------------
% (12006)------------------------------
% (12031)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (12007)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% (12031)Refutation not found, incomplete strategy% (12031)------------------------------
% (12031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12031)Termination reason: Refutation not found, incomplete strategy

% (12031)Memory used [KB]: 6268
% (12031)Time elapsed: 0.136 s
% (12031)------------------------------
% (12031)------------------------------
% (12030)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (12030)Refutation not found, incomplete strategy% (12030)------------------------------
% (12030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12030)Termination reason: Refutation not found, incomplete strategy

% (12030)Memory used [KB]: 6268
% (12030)Time elapsed: 0.148 s
% (12030)------------------------------
% (12030)------------------------------
% (12021)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (12021)Refutation not found, incomplete strategy% (12021)------------------------------
% (12021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12021)Termination reason: Refutation not found, incomplete strategy

% (12021)Memory used [KB]: 10618
% (12021)Time elapsed: 0.157 s
% (12021)------------------------------
% (12021)------------------------------
% (12033)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

% (12019)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) )
   => ( sK0 != sK1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

% (12019)Refutation not found, incomplete strategy% (12019)------------------------------
% (12019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12019)Termination reason: Refutation not found, incomplete strategy

% (12019)Memory used [KB]: 1663
% (12019)Time elapsed: 0.157 s
% (12019)------------------------------
% (12019)------------------------------
fof(f20,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f61,f62,f60,f68])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f113,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f34,f86])).

fof(f86,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f68])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f34,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f185,plain,(
    r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)) ),
    inference(superposition,[],[f166,f146])).

fof(f146,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0) ),
    inference(forward_demodulation,[],[f144,f36])).

fof(f144,plain,(
    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0) ),
    inference(superposition,[],[f69,f128])).

fof(f128,plain,(
    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f70,f118])).

fof(f166,plain,(
    ! [X12] : r2_hidden(X12,k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X12)) ),
    inference(superposition,[],[f88,f143])).

fof(f143,plain,(
    ! [X9] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X9) ),
    inference(forward_demodulation,[],[f141,f69])).

fof(f141,plain,(
    ! [X9] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))) ),
    inference(superposition,[],[f69,f118])).

fof(f88,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f53,f66])).

% (12034)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f29])).

% (12034)Refutation not found, incomplete strategy% (12034)------------------------------
% (12034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12034)Termination reason: Refutation not found, incomplete strategy

% (12034)Memory used [KB]: 1663
% (12034)Time elapsed: 0.002 s
% (12034)------------------------------
% (12034)------------------------------
fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:50:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (12032)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (12017)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (12017)Refutation not found, incomplete strategy% (12017)------------------------------
% 0.21/0.51  % (12017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12017)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12017)Memory used [KB]: 10618
% 0.21/0.51  % (12017)Time elapsed: 0.101 s
% 0.21/0.51  % (12017)------------------------------
% 0.21/0.51  % (12017)------------------------------
% 0.21/0.52  % (12032)Refutation not found, incomplete strategy% (12032)------------------------------
% 0.21/0.52  % (12032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12032)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12032)Memory used [KB]: 6140
% 0.21/0.52  % (12032)Time elapsed: 0.092 s
% 0.21/0.52  % (12032)------------------------------
% 0.21/0.52  % (12032)------------------------------
% 0.21/0.52  % (12011)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (12023)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (12023)Refutation not found, incomplete strategy% (12023)------------------------------
% 0.21/0.53  % (12023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12023)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12023)Memory used [KB]: 1663
% 0.21/0.53  % (12023)Time elapsed: 0.071 s
% 0.21/0.53  % (12023)------------------------------
% 0.21/0.53  % (12023)------------------------------
% 0.21/0.53  % (12009)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (12026)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (12005)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (12010)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (12024)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (12016)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (12014)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (12016)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (12013)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (12028)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (12022)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (12012)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (12027)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f185,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 0.21/0.55    inference(backward_demodulation,[],[f113,f118])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),
% 0.21/0.55    inference(superposition,[],[f117,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f117,plain,(
% 0.21/0.55    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f116,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f48,f65,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f49,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f58,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f59,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_enumset1)).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK1,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f114,f75])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f69,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)))),
% 0.21/0.55    inference(definition_unfolding,[],[f33,f41,f68,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f37,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f39,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.55    inference(definition_unfolding,[],[f46,f65])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  % (12008)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (12006)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (12015)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (12006)Refutation not found, incomplete strategy% (12006)------------------------------
% 0.21/0.56  % (12006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12006)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12006)Memory used [KB]: 1663
% 0.21/0.56  % (12006)Time elapsed: 0.145 s
% 0.21/0.56  % (12006)------------------------------
% 0.21/0.56  % (12006)------------------------------
% 0.21/0.56  % (12031)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (12007)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (12031)Refutation not found, incomplete strategy% (12031)------------------------------
% 0.21/0.56  % (12031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12031)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12031)Memory used [KB]: 6268
% 0.21/0.56  % (12031)Time elapsed: 0.136 s
% 0.21/0.56  % (12031)------------------------------
% 0.21/0.56  % (12031)------------------------------
% 0.21/0.56  % (12030)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (12030)Refutation not found, incomplete strategy% (12030)------------------------------
% 0.21/0.56  % (12030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12030)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12030)Memory used [KB]: 6268
% 0.21/0.56  % (12030)Time elapsed: 0.148 s
% 0.21/0.56  % (12030)------------------------------
% 0.21/0.56  % (12030)------------------------------
% 0.21/0.56  % (12021)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (12021)Refutation not found, incomplete strategy% (12021)------------------------------
% 0.21/0.56  % (12021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (12021)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (12021)Memory used [KB]: 10618
% 0.21/0.56  % (12021)Time elapsed: 0.157 s
% 0.21/0.56  % (12021)------------------------------
% 0.21/0.56  % (12021)------------------------------
% 0.21/0.56  % (12033)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  % (12019)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.56/0.56  fof(f33,plain,(
% 1.56/0.56    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.56/0.56    inference(cnf_transformation,[],[f23])).
% 1.56/0.56  fof(f23,plain,(
% 1.56/0.56    sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 1.56/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 1.56/0.56  fof(f22,plain,(
% 1.56/0.56    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) => (sK0 != sK1 & k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.56/0.56    introduced(choice_axiom,[])).
% 1.56/0.56  % (12019)Refutation not found, incomplete strategy% (12019)------------------------------
% 1.56/0.56  % (12019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.56  % (12019)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.56  
% 1.56/0.56  % (12019)Memory used [KB]: 1663
% 1.56/0.56  % (12019)Time elapsed: 0.157 s
% 1.56/0.56  % (12019)------------------------------
% 1.56/0.56  % (12019)------------------------------
% 1.56/0.56  fof(f20,plain,(
% 1.56/0.56    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.56/0.56    inference(ennf_transformation,[],[f19])).
% 1.56/0.56  fof(f19,negated_conjecture,(
% 1.56/0.56    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.56/0.56    inference(negated_conjecture,[],[f18])).
% 1.56/0.56  fof(f18,conjecture,(
% 1.56/0.56    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 1.56/0.56  fof(f69,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))))) )),
% 1.56/0.56    inference(definition_unfolding,[],[f61,f62,f60,f68])).
% 1.56/0.56  fof(f62,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.56/0.56    inference(definition_unfolding,[],[f40,f41])).
% 1.56/0.56  fof(f40,plain,(
% 1.56/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f6])).
% 1.56/0.56  fof(f6,axiom,(
% 1.56/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.56/0.56  fof(f61,plain,(
% 1.56/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 1.56/0.56    inference(cnf_transformation,[],[f10])).
% 1.56/0.56  fof(f10,axiom,(
% 1.56/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 1.56/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 1.56/0.56  fof(f113,plain,(
% 1.56/0.56    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.56/0.56    inference(unit_resulting_resolution,[],[f34,f86])).
% 1.56/0.56  fof(f86,plain,(
% 1.56/0.56    ( ! [X0,X3] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X3) )),
% 1.56/0.56    inference(equality_resolution,[],[f74])).
% 1.56/0.57  fof(f74,plain,(
% 1.56/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 1.56/0.57    inference(definition_unfolding,[],[f42,f68])).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.56/0.57    inference(rectify,[],[f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    sK0 != sK1),
% 1.56/0.57    inference(cnf_transformation,[],[f23])).
% 1.56/0.57  fof(f185,plain,(
% 1.56/0.57    r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))),
% 1.56/0.57    inference(superposition,[],[f166,f146])).
% 1.56/0.57  fof(f146,plain,(
% 1.56/0.57    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0)),
% 1.56/0.57    inference(forward_demodulation,[],[f144,f36])).
% 1.56/0.57  fof(f144,plain,(
% 1.56/0.57    k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,sK0)),
% 1.56/0.57    inference(superposition,[],[f69,f128])).
% 1.56/0.57  fof(f128,plain,(
% 1.56/0.57    k1_xboole_0 = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1)))),
% 1.56/0.57    inference(backward_demodulation,[],[f70,f118])).
% 1.56/0.57  fof(f166,plain,(
% 1.56/0.57    ( ! [X12] : (r2_hidden(X12,k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X12))) )),
% 1.56/0.57    inference(superposition,[],[f88,f143])).
% 1.56/0.57  fof(f143,plain,(
% 1.56/0.57    ( ! [X9] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9) = k6_enumset1(sK0,sK0,sK0,sK0,sK1,sK1,sK1,X9)) )),
% 1.56/0.57    inference(forward_demodulation,[],[f141,f69])).
% 1.56/0.57  fof(f141,plain,(
% 1.56/0.57    ( ! [X9] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X9) = k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1),k5_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k3_xboole_0(k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK1,sK1))))) )),
% 1.56/0.57    inference(superposition,[],[f69,f118])).
% 1.56/0.57  fof(f88,plain,(
% 1.56/0.57    ( ! [X0,X5,X1] : (r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5))) )),
% 1.56/0.57    inference(equality_resolution,[],[f87])).
% 1.56/0.57  fof(f87,plain,(
% 1.56/0.57    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X5) != X3) )),
% 1.56/0.57    inference(equality_resolution,[],[f80])).
% 1.56/0.57  fof(f80,plain,(
% 1.56/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.56/0.57    inference(definition_unfolding,[],[f53,f66])).
% 1.56/0.57  % (12034)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.57  fof(f53,plain,(
% 1.56/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.56/0.57    inference(cnf_transformation,[],[f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.57    inference(rectify,[],[f29])).
% 1.56/0.57  % (12034)Refutation not found, incomplete strategy% (12034)------------------------------
% 1.56/0.57  % (12034)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (12034)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (12034)Memory used [KB]: 1663
% 1.56/0.57  % (12034)Time elapsed: 0.002 s
% 1.56/0.57  % (12034)------------------------------
% 1.56/0.57  % (12034)------------------------------
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.57    inference(flattening,[],[f28])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.56/0.57    inference(nnf_transformation,[],[f21])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.56/0.57    inference(ennf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (12016)------------------------------
% 1.56/0.57  % (12016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (12016)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (12016)Memory used [KB]: 6396
% 1.56/0.57  % (12016)Time elapsed: 0.120 s
% 1.56/0.57  % (12016)------------------------------
% 1.56/0.57  % (12016)------------------------------
% 1.56/0.57  % (12025)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.57  % (12004)Success in time 0.209 s
%------------------------------------------------------------------------------
