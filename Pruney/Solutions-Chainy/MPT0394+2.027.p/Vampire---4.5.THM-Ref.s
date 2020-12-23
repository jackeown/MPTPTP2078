%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:59 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 106 expanded)
%              Number of leaves         :   14 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  169 ( 323 expanded)
%              Number of equality atoms :  135 ( 256 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(subsumption_resolution,[],[f49,f122])).

% (19017)Refutation not found, incomplete strategy% (19017)------------------------------
% (19017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19017)Termination reason: Refutation not found, incomplete strategy

% (19017)Memory used [KB]: 10618
% (19017)Time elapsed: 0.094 s
% (19017)------------------------------
% (19017)------------------------------
% (19015)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (19009)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (19001)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (19007)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (18998)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (18995)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (18995)Refutation not found, incomplete strategy% (18995)------------------------------
% (18995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18995)Termination reason: Refutation not found, incomplete strategy

% (18995)Memory used [KB]: 1663
% (18995)Time elapsed: 0.127 s
% (18995)------------------------------
% (18995)------------------------------
% (18996)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (19008)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (19011)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (19015)Refutation not found, incomplete strategy% (19015)------------------------------
% (19015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19015)Termination reason: Refutation not found, incomplete strategy

% (19015)Memory used [KB]: 10746
% (19015)Time elapsed: 0.134 s
% (19015)------------------------------
% (19015)------------------------------
% (19020)Refutation not found, incomplete strategy% (19020)------------------------------
% (19020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19020)Termination reason: Refutation not found, incomplete strategy

% (19020)Memory used [KB]: 6268
% (19020)Time elapsed: 0.142 s
% (19020)------------------------------
% (19020)------------------------------
% (19024)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (19002)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (19003)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (19003)Refutation not found, incomplete strategy% (19003)------------------------------
% (19003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19003)Termination reason: Refutation not found, incomplete strategy

% (19003)Memory used [KB]: 10618
% (19003)Time elapsed: 0.140 s
% (19003)------------------------------
% (19003)------------------------------
% (19014)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (19019)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f122,plain,(
    ! [X0,X1] : k1_setfam_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(subsumption_resolution,[],[f115,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(subsumption_resolution,[],[f69,f78])).

fof(f78,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f75,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f31,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f75,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(superposition,[],[f66,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f66,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f39,f46])).

% (18997)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f39,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK2(X0,X1,X2,X3) != X2
              & sK2(X0,X1,X2,X3) != X1
              & sK2(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( sK2(X0,X1,X2,X3) = X2
            | sK2(X0,X1,X2,X3) = X1
            | sK2(X0,X1,X2,X3) = X0
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).

fof(f24,plain,(
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
     => ( ( ( sK2(X0,X1,X2,X3) != X2
            & sK2(X0,X1,X2,X3) != X1
            & sK2(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( sK2(X0,X1,X2,X3) = X2
          | sK2(X0,X1,X2,X3) = X1
          | sK2(X0,X1,X2,X3) = X0
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tarski(X0)
      | ~ r2_hidden(X0,k1_tarski(X0)) ) ),
    inference(superposition,[],[f36,f68])).

fof(f68,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f52,f35])).

fof(f35,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f109,f28])).

fof(f28,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1 ) ),
    inference(subsumption_resolution,[],[f105,f80])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f50,f28])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f27,f32])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f49,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(definition_unfolding,[],[f26,f32,f29])).

fof(f26,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:44:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (19004)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.47  % (19004)Refutation not found, incomplete strategy% (19004)------------------------------
% 0.21/0.47  % (19004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19004)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19004)Memory used [KB]: 10618
% 0.21/0.47  % (19004)Time elapsed: 0.064 s
% 0.21/0.47  % (19004)------------------------------
% 0.21/0.47  % (19004)------------------------------
% 0.21/0.47  % (19012)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.47  % (19012)Refutation not found, incomplete strategy% (19012)------------------------------
% 0.21/0.47  % (19012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19012)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19012)Memory used [KB]: 10618
% 0.21/0.47  % (19012)Time elapsed: 0.065 s
% 0.21/0.47  % (19012)------------------------------
% 0.21/0.47  % (19012)------------------------------
% 0.21/0.51  % (19023)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (19006)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (18999)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.51  % (18999)Refutation not found, incomplete strategy% (18999)------------------------------
% 1.22/0.51  % (18999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (18999)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.51  
% 1.22/0.51  % (18999)Memory used [KB]: 6268
% 1.22/0.51  % (18999)Time elapsed: 0.110 s
% 1.22/0.51  % (18999)------------------------------
% 1.22/0.51  % (18999)------------------------------
% 1.22/0.51  % (19000)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.51  % (19005)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.22/0.51  % (19020)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.22/0.51  % (19005)Refutation not found, incomplete strategy% (19005)------------------------------
% 1.22/0.51  % (19005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (19005)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.51  
% 1.22/0.51  % (19005)Memory used [KB]: 10618
% 1.22/0.51  % (19005)Time elapsed: 0.118 s
% 1.22/0.51  % (19005)------------------------------
% 1.22/0.51  % (19005)------------------------------
% 1.22/0.51  % (19017)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.22/0.52  % (19000)Refutation found. Thanks to Tanya!
% 1.22/0.52  % SZS status Theorem for theBenchmark
% 1.22/0.52  % SZS output start Proof for theBenchmark
% 1.22/0.52  fof(f123,plain,(
% 1.22/0.52    $false),
% 1.22/0.52    inference(subsumption_resolution,[],[f49,f122])).
% 1.22/0.52  % (19017)Refutation not found, incomplete strategy% (19017)------------------------------
% 1.22/0.52  % (19017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (19017)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (19017)Memory used [KB]: 10618
% 1.22/0.52  % (19017)Time elapsed: 0.094 s
% 1.22/0.52  % (19017)------------------------------
% 1.22/0.52  % (19017)------------------------------
% 1.22/0.52  % (19015)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.52  % (19009)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.22/0.52  % (19001)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.52  % (19007)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (18998)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.53  % (18995)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.53  % (18995)Refutation not found, incomplete strategy% (18995)------------------------------
% 1.38/0.53  % (18995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (18995)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (18995)Memory used [KB]: 1663
% 1.38/0.53  % (18995)Time elapsed: 0.127 s
% 1.38/0.53  % (18995)------------------------------
% 1.38/0.53  % (18995)------------------------------
% 1.38/0.53  % (18996)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.53  % (19008)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.53  % (19011)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.53  % (19015)Refutation not found, incomplete strategy% (19015)------------------------------
% 1.38/0.53  % (19015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (19015)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (19015)Memory used [KB]: 10746
% 1.38/0.53  % (19015)Time elapsed: 0.134 s
% 1.38/0.53  % (19015)------------------------------
% 1.38/0.53  % (19015)------------------------------
% 1.38/0.53  % (19020)Refutation not found, incomplete strategy% (19020)------------------------------
% 1.38/0.53  % (19020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (19020)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (19020)Memory used [KB]: 6268
% 1.38/0.53  % (19020)Time elapsed: 0.142 s
% 1.38/0.53  % (19020)------------------------------
% 1.38/0.53  % (19020)------------------------------
% 1.38/0.54  % (19024)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.54  % (19002)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.54  % (19003)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (19003)Refutation not found, incomplete strategy% (19003)------------------------------
% 1.38/0.54  % (19003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (19003)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (19003)Memory used [KB]: 10618
% 1.38/0.54  % (19003)Time elapsed: 0.140 s
% 1.38/0.54  % (19003)------------------------------
% 1.38/0.54  % (19003)------------------------------
% 1.38/0.54  % (19014)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.54  % (19019)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.54  fof(f122,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f115,f80])).
% 1.38/0.54  fof(f80,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f69,f78])).
% 1.38/0.54  fof(f78,plain,(
% 1.38/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.38/0.54    inference(superposition,[],[f75,f48])).
% 1.38/0.54  fof(f48,plain,(
% 1.38/0.54    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f31,f29])).
% 1.38/0.54  fof(f29,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.38/0.54    inference(cnf_transformation,[],[f5])).
% 1.38/0.54  fof(f5,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.38/0.54  fof(f31,plain,(
% 1.38/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f6])).
% 1.38/0.54  fof(f6,axiom,(
% 1.38/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.54  fof(f75,plain,(
% 1.38/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 1.38/0.54    inference(superposition,[],[f66,f51])).
% 1.38/0.54  fof(f51,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.38/0.54    inference(definition_unfolding,[],[f30,f29,f46])).
% 1.38/0.54  fof(f46,plain,(
% 1.38/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f8])).
% 1.38/0.54  fof(f8,axiom,(
% 1.38/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.38/0.54  fof(f30,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f7])).
% 1.38/0.54  fof(f7,axiom,(
% 1.38/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.38/0.54  fof(f66,plain,(
% 1.38/0.54    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.38/0.54    inference(equality_resolution,[],[f65])).
% 1.38/0.54  fof(f65,plain,(
% 1.38/0.54    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.38/0.54    inference(equality_resolution,[],[f59])).
% 1.38/0.54  fof(f59,plain,(
% 1.38/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.38/0.54    inference(definition_unfolding,[],[f39,f46])).
% 1.38/0.54  % (18997)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  fof(f39,plain,(
% 1.38/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.38/0.54    inference(cnf_transformation,[],[f25])).
% 1.38/0.54  fof(f25,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f24])).
% 1.38/0.54  fof(f24,plain,(
% 1.38/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f23,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(rectify,[],[f22])).
% 1.38/0.54  fof(f22,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(flattening,[],[f21])).
% 1.38/0.54  fof(f21,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.38/0.54    inference(nnf_transformation,[],[f17])).
% 1.38/0.54  fof(f17,plain,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.38/0.54    inference(ennf_transformation,[],[f4])).
% 1.38/0.54  fof(f4,axiom,(
% 1.38/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.38/0.54  fof(f69,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0) | ~r2_hidden(X0,k1_tarski(X0))) )),
% 1.38/0.54    inference(superposition,[],[f36,f68])).
% 1.38/0.54  fof(f68,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.38/0.54    inference(backward_demodulation,[],[f52,f35])).
% 1.38/0.54  fof(f35,plain,(
% 1.38/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f2])).
% 1.38/0.54  fof(f2,axiom,(
% 1.38/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.38/0.54  fof(f52,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.38/0.54    inference(definition_unfolding,[],[f33,f32])).
% 1.38/0.54  fof(f32,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f3])).
% 1.38/0.54  fof(f3,axiom,(
% 1.38/0.54    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.38/0.54  fof(f33,plain,(
% 1.38/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f1])).
% 1.38/0.54  fof(f1,axiom,(
% 1.38/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.38/0.54  fof(f36,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.38/0.54    inference(cnf_transformation,[],[f20])).
% 1.38/0.54  fof(f20,plain,(
% 1.38/0.54    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.38/0.54    inference(nnf_transformation,[],[f10])).
% 1.38/0.54  fof(f10,axiom,(
% 1.38/0.54    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.38/0.54  fof(f115,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.38/0.54    inference(superposition,[],[f109,f28])).
% 1.38/0.54  fof(f28,plain,(
% 1.38/0.54    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f12])).
% 1.38/0.54  fof(f12,axiom,(
% 1.38/0.54    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.38/0.54  fof(f109,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1) )),
% 1.38/0.54    inference(subsumption_resolution,[],[f105,f80])).
% 1.38/0.54  fof(f105,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = k1_tarski(X0)) )),
% 1.38/0.54    inference(superposition,[],[f50,f28])).
% 1.38/0.54  fof(f50,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k4_xboole_0(k1_setfam_1(X0),k4_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.54    inference(definition_unfolding,[],[f27,f32])).
% 1.38/0.54  fof(f27,plain,(
% 1.38/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.38/0.54    inference(cnf_transformation,[],[f16])).
% 1.38/0.54  fof(f16,plain,(
% 1.38/0.54    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.38/0.54    inference(ennf_transformation,[],[f11])).
% 1.38/0.54  fof(f11,axiom,(
% 1.38/0.54    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.38/0.54  fof(f49,plain,(
% 1.38/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_setfam_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 1.38/0.54    inference(definition_unfolding,[],[f26,f32,f29])).
% 1.38/0.54  fof(f26,plain,(
% 1.38/0.54    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.38/0.54    inference(cnf_transformation,[],[f19])).
% 1.38/0.54  fof(f19,plain,(
% 1.38/0.54    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.38/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f18])).
% 1.38/0.54  fof(f18,plain,(
% 1.38/0.54    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.38/0.54    introduced(choice_axiom,[])).
% 1.38/0.54  fof(f15,plain,(
% 1.38/0.54    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.54    inference(ennf_transformation,[],[f14])).
% 1.38/0.54  fof(f14,negated_conjecture,(
% 1.38/0.54    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.54    inference(negated_conjecture,[],[f13])).
% 1.38/0.54  fof(f13,conjecture,(
% 1.38/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.38/0.54  % SZS output end Proof for theBenchmark
% 1.38/0.54  % (19000)------------------------------
% 1.38/0.54  % (19000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (19000)Termination reason: Refutation
% 1.38/0.54  
% 1.38/0.54  % (19000)Memory used [KB]: 6268
% 1.38/0.54  % (19000)Time elapsed: 0.121 s
% 1.38/0.54  % (19000)------------------------------
% 1.38/0.54  % (19000)------------------------------
% 1.38/0.54  % (18994)Success in time 0.183 s
%------------------------------------------------------------------------------
