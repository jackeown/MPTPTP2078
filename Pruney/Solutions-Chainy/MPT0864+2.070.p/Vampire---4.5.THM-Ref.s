%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 619 expanded)
%              Number of leaves         :   12 ( 193 expanded)
%              Depth                    :   17
%              Number of atoms          :  135 ( 940 expanded)
%              Number of equality atoms :   97 ( 701 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23467)Refutation not found, incomplete strategy% (23467)------------------------------
% (23467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f231,plain,(
    $false ),
    inference(global_subsumption,[],[f66,f226,f228])).

fof(f228,plain,(
    sK0 != sK2 ),
    inference(superposition,[],[f223,f18])).

fof(f18,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f223,plain,(
    ! [X4,X3] : k4_tarski(X4,X3) != X3 ),
    inference(subsumption_resolution,[],[f216,f106])).

fof(f106,plain,(
    ! [X1] : k1_xboole_0 != k2_enumset1(X1,X1,X1,X1) ),
    inference(backward_demodulation,[],[f62,f104])).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(subsumption_resolution,[],[f102,f22])).

fof(f22,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0))
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f79,f45])).

fof(f45,plain,(
    ! [X0] : k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f23,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f24,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(k5_xboole_0(X0,X0)),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))))
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f78,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f42])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k5_xboole_0(X0,X0)),X0)
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f77,f22])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f60,f45])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f35,f43])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(forward_demodulation,[],[f57,f45])).

fof(f57,plain,(
    ! [X1] : k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f30,f44,f43,f44,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f41])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f216,plain,(
    ! [X4,X3] :
      ( k4_tarski(X4,X3) != X3
      | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3) ) ),
    inference(superposition,[],[f74,f211])).

fof(f211,plain,(
    ! [X0] : sK3(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(subsumption_resolution,[],[f210,f106])).

fof(f210,plain,(
    ! [X0] :
      ( sK3(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,(
    ! [X0] :
      ( sK3(k2_enumset1(X0,X0,X0,X0)) = X0
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)
      | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) ) ),
    inference(resolution,[],[f113,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0))))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f59,f22])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1)))))
      | sK3(X0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f54,f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2))))) ) ),
    inference(definition_unfolding,[],[f40,f43,f44])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | X0 = X2
      | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK3(X0) != k4_tarski(X1,sK3(X0))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | sK3(X0) != k4_tarski(X1,sK3(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f21,f22])).

fof(f21,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0
      | k4_tarski(X2,X3) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f226,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f222,f18])).

fof(f222,plain,(
    ! [X2,X1] : k4_tarski(X1,X2) != X1 ),
    inference(subsumption_resolution,[],[f215,f106])).

fof(f215,plain,(
    ! [X2,X1] :
      ( k4_tarski(X1,X2) != X1
      | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1) ) ),
    inference(superposition,[],[f72,f211])).

fof(f72,plain,(
    ! [X0,X1] :
      ( sK3(X0) != k4_tarski(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | sK3(X0) != k4_tarski(sK3(X0),X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f20,f22])).

fof(f20,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X0
      | k4_tarski(X2,X3) != sK3(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f65,f64])).

fof(f64,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f17,f63])).

fof(f63,plain,(
    sK1 = k1_mcart_1(sK0) ),
    inference(superposition,[],[f27,f18])).

fof(f27,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f17,plain,
    ( sK0 = k1_mcart_1(sK0)
    | sK0 = k2_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    sK2 = k2_mcart_1(sK0) ),
    inference(superposition,[],[f28,f18])).

fof(f28,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:27:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (23447)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (23473)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.51  % (23447)Refutation not found, incomplete strategy% (23447)------------------------------
% 0.22/0.51  % (23447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23447)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23447)Memory used [KB]: 1663
% 0.22/0.51  % (23447)Time elapsed: 0.092 s
% 0.22/0.51  % (23447)------------------------------
% 0.22/0.51  % (23447)------------------------------
% 0.22/0.52  % (23461)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (23473)Refutation not found, incomplete strategy% (23473)------------------------------
% 0.22/0.52  % (23473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23473)Memory used [KB]: 10746
% 0.22/0.52  % (23473)Time elapsed: 0.097 s
% 0.22/0.52  % (23473)------------------------------
% 0.22/0.52  % (23473)------------------------------
% 0.22/0.52  % (23457)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (23457)Refutation not found, incomplete strategy% (23457)------------------------------
% 0.22/0.52  % (23457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23457)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23457)Memory used [KB]: 10618
% 0.22/0.52  % (23457)Time elapsed: 0.108 s
% 0.22/0.52  % (23457)------------------------------
% 0.22/0.52  % (23457)------------------------------
% 0.22/0.53  % (23456)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (23456)Refutation not found, incomplete strategy% (23456)------------------------------
% 0.22/0.53  % (23456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23452)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (23453)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (23449)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (23470)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (23448)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (23462)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (23474)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (23456)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23456)Memory used [KB]: 10618
% 0.22/0.54  % (23456)Time elapsed: 0.116 s
% 0.22/0.54  % (23456)------------------------------
% 0.22/0.54  % (23456)------------------------------
% 0.22/0.54  % (23449)Refutation not found, incomplete strategy% (23449)------------------------------
% 0.22/0.54  % (23449)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23470)Refutation not found, incomplete strategy% (23470)------------------------------
% 0.22/0.54  % (23470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23465)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (23475)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (23462)Refutation not found, incomplete strategy% (23462)------------------------------
% 0.22/0.54  % (23462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23467)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (23453)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (23454)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (23470)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23470)Memory used [KB]: 1791
% 0.22/0.54  % (23470)Time elapsed: 0.087 s
% 0.22/0.54  % (23470)------------------------------
% 0.22/0.54  % (23470)------------------------------
% 0.22/0.54  % (23462)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23462)Memory used [KB]: 6140
% 0.22/0.54  % (23462)Time elapsed: 0.006 s
% 0.22/0.54  % (23462)------------------------------
% 0.22/0.54  % (23462)------------------------------
% 0.22/0.54  % (23466)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (23476)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (23459)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (23460)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (23449)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23449)Memory used [KB]: 10746
% 0.22/0.55  % (23449)Time elapsed: 0.122 s
% 0.22/0.55  % (23449)------------------------------
% 0.22/0.55  % (23449)------------------------------
% 0.22/0.55  % (23469)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.55  % (23469)Refutation not found, incomplete strategy% (23469)------------------------------
% 0.22/0.55  % (23469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23469)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23469)Memory used [KB]: 10746
% 0.22/0.55  % (23469)Time elapsed: 0.139 s
% 0.22/0.55  % (23469)------------------------------
% 0.22/0.55  % (23469)------------------------------
% 0.22/0.55  % (23472)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (23472)Refutation not found, incomplete strategy% (23472)------------------------------
% 0.22/0.55  % (23472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23472)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (23472)Memory used [KB]: 6268
% 0.22/0.55  % (23472)Time elapsed: 0.141 s
% 0.22/0.55  % (23472)------------------------------
% 0.22/0.55  % (23472)------------------------------
% 0.22/0.56  % (23464)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (23464)Refutation not found, incomplete strategy% (23464)------------------------------
% 0.22/0.56  % (23464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23464)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (23464)Memory used [KB]: 10618
% 0.22/0.56  % (23464)Time elapsed: 0.143 s
% 0.22/0.56  % (23464)------------------------------
% 0.22/0.56  % (23464)------------------------------
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  % (23467)Refutation not found, incomplete strategy% (23467)------------------------------
% 0.22/0.56  % (23467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(global_subsumption,[],[f66,f226,f228])).
% 0.22/0.56  fof(f228,plain,(
% 0.22/0.56    sK0 != sK2),
% 0.22/0.56    inference(superposition,[],[f223,f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.56    inference(negated_conjecture,[],[f12])).
% 0.22/0.56  fof(f12,conjecture,(
% 0.22/0.56    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.22/0.56  fof(f223,plain,(
% 0.22/0.56    ( ! [X4,X3] : (k4_tarski(X4,X3) != X3) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f216,f106])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ( ! [X1] : (k1_xboole_0 != k2_enumset1(X1,X1,X1,X1)) )),
% 0.22/0.56    inference(backward_demodulation,[],[f62,f104])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f102,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ( ! [X0] : (~r2_hidden(sK3(k5_xboole_0(X0,X0)),k5_xboole_0(X0,X0)) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(superposition,[],[f79,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ( ! [X0] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.22/0.56    inference(definition_unfolding,[],[f23,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f24,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f25,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.56    inference(rectify,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(k5_xboole_0(X0,X0)),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f78,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) )),
% 0.22/0.56    inference(equality_resolution,[],[f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != X2) )),
% 0.22/0.56    inference(definition_unfolding,[],[f36,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f26,f42])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X0] : (r2_hidden(sK3(k5_xboole_0(X0,X0)),X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f77,f22])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 0.22/0.56    inference(superposition,[],[f60,f45])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) | r2_hidden(X3,X0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) != X2) )),
% 0.22/0.56    inference(definition_unfolding,[],[f35,f43])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f57,f45])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X1] : (k2_enumset1(X1,X1,X1,X1) != k5_xboole_0(k2_enumset1(X1,X1,X1,X1),k1_setfam_1(k2_enumset1(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.22/0.56    inference(equality_resolution,[],[f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (X0 != X1 | k2_enumset1(X0,X0,X0,X0) != k5_xboole_0(k2_enumset1(X0,X0,X0,X0),k1_setfam_1(k2_enumset1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f30,f44,f43,f44,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.56    inference(definition_unfolding,[],[f19,f41])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    ( ! [X4,X3] : (k4_tarski(X4,X3) != X3 | k1_xboole_0 = k2_enumset1(X3,X3,X3,X3)) )),
% 0.22/0.56    inference(superposition,[],[f74,f211])).
% 0.22/0.56  fof(f211,plain,(
% 0.22/0.56    ( ! [X0] : (sK3(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f210,f106])).
% 0.22/0.56  fof(f210,plain,(
% 0.22/0.56    ( ! [X0] : (sK3(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f200])).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    ( ! [X0] : (sK3(k2_enumset1(X0,X0,X0,X0)) = X0 | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0) | k1_xboole_0 = k2_enumset1(X0,X0,X0,X0)) )),
% 0.22/0.56    inference(resolution,[],[f113,f75])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0),k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,X0)))) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f59,f22])).
% 0.22/0.56  fof(f113,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0),k5_xboole_0(X0,k1_setfam_1(k2_enumset1(X0,X0,X0,k2_enumset1(X1,X1,X1,X1))))) | sK3(X0) = X1 | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f54,f22])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k2_enumset1(X1,X1,X1,k2_enumset1(X2,X2,X2,X2)))))) )),
% 0.22/0.56    inference(definition_unfolding,[],[f40,f43,f44])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | X0 = X2 | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sK3(X0) != k4_tarski(X1,sK3(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | sK3(X0) != k4_tarski(X1,sK3(X0)) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f21,f22])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK3(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f226,plain,(
% 0.22/0.56    sK0 != sK1),
% 0.22/0.56    inference(superposition,[],[f222,f18])).
% 0.22/0.56  fof(f222,plain,(
% 0.22/0.56    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f215,f106])).
% 0.22/0.56  fof(f215,plain,(
% 0.22/0.56    ( ! [X2,X1] : (k4_tarski(X1,X2) != X1 | k1_xboole_0 = k2_enumset1(X1,X1,X1,X1)) )),
% 0.22/0.56    inference(superposition,[],[f72,f211])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sK3(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f71])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | sK3(X0) != k4_tarski(sK3(X0),X1) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f20,f22])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k1_xboole_0 = X0 | k4_tarski(X2,X3) != sK3(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    sK0 = sK2 | sK0 = sK1),
% 0.22/0.56    inference(superposition,[],[f65,f64])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.22/0.56    inference(backward_demodulation,[],[f17,f63])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    sK1 = k1_mcart_1(sK0)),
% 0.22/0.56    inference(superposition,[],[f27,f18])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    sK0 = k1_mcart_1(sK0) | sK0 = k2_mcart_1(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f15])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    sK2 = k2_mcart_1(sK0)),
% 0.22/0.56    inference(superposition,[],[f28,f18])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (23453)------------------------------
% 0.22/0.56  % (23453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (23453)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (23453)Memory used [KB]: 6524
% 0.22/0.56  % (23453)Time elapsed: 0.125 s
% 0.22/0.56  % (23453)------------------------------
% 0.22/0.56  % (23453)------------------------------
% 0.22/0.56  % (23446)Success in time 0.188 s
%------------------------------------------------------------------------------
