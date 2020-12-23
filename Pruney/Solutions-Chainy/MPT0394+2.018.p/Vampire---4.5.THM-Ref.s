%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:58 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 118 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 344 expanded)
%              Number of equality atoms :  136 ( 261 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f110,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,(
    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f27,f106])).

fof(f106,plain,(
    ! [X8,X7] : k1_setfam_1(k2_tarski(X7,X8)) = k3_xboole_0(X7,X8) ),
    inference(forward_demodulation,[],[f105,f49])).

fof(f49,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f105,plain,(
    ! [X8,X7] : k1_setfam_1(k2_tarski(X7,X8)) = k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),X8) ),
    inference(forward_demodulation,[],[f104,f49])).

fof(f104,plain,(
    ! [X8,X7] : k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),k1_setfam_1(k2_tarski(X8,X8))) = k1_setfam_1(k2_tarski(X7,X8)) ),
    inference(subsumption_resolution,[],[f103,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 != k2_tarski(X0,X0) ),
    inference(subsumption_resolution,[],[f71,f68])).

fof(f68,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f65,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f40,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

% (11511)Refutation not found, incomplete strategy% (11511)------------------------------
% (11511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11520)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (11511)Termination reason: Refutation not found, incomplete strategy

% (11511)Memory used [KB]: 10618
% (11511)Time elapsed: 0.143 s
% (11511)------------------------------
% (11511)------------------------------
% (11503)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (11520)Refutation not found, incomplete strategy% (11520)------------------------------
% (11520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f25,plain,(
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

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f71,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_tarski(X0,X0)
      | ~ r2_hidden(X0,k2_tarski(X0,X0)) ) ),
    inference(superposition,[],[f67,f30])).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k3_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f29])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f8])).

% (11508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f103,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),k1_setfam_1(k2_tarski(X8,X8))) = k1_setfam_1(k2_tarski(X7,X8))
      | k1_xboole_0 = k2_tarski(X7,X7) ) ),
    inference(subsumption_resolution,[],[f98,f72])).

fof(f98,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),k1_setfam_1(k2_tarski(X8,X8))) = k1_setfam_1(k2_tarski(X7,X8))
      | k1_xboole_0 = k2_tarski(X8,X8)
      | k1_xboole_0 = k2_tarski(X7,X7) ) ),
    inference(superposition,[],[f50,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(superposition,[],[f73,f47])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))) ),
    inference(superposition,[],[f48,f47])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_enumset1(X0,X0,X1,X2),k2_tarski(X3,X3))) ),
    inference(definition_unfolding,[],[f38,f31,f37,f29])).

fof(f31,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1)))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f31])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f27,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).

fof(f19,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n010.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:31:59 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.56  % (11497)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  % (11497)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (11496)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.58  % (11511)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.58  % (11499)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.46/0.58  % (11505)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.58  % SZS output start Proof for theBenchmark
% 1.46/0.58  fof(f110,plain,(
% 1.46/0.58    $false),
% 1.46/0.58    inference(trivial_inequality_removal,[],[f108])).
% 1.46/0.58  fof(f108,plain,(
% 1.46/0.58    k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)),
% 1.46/0.58    inference(superposition,[],[f27,f106])).
% 1.46/0.58  fof(f106,plain,(
% 1.46/0.58    ( ! [X8,X7] : (k1_setfam_1(k2_tarski(X7,X8)) = k3_xboole_0(X7,X8)) )),
% 1.46/0.58    inference(forward_demodulation,[],[f105,f49])).
% 1.46/0.58  fof(f49,plain,(
% 1.46/0.58    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,X0)) = X0) )),
% 1.46/0.58    inference(definition_unfolding,[],[f28,f29])).
% 1.46/0.58  fof(f29,plain,(
% 1.46/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f5])).
% 1.46/0.58  fof(f5,axiom,(
% 1.46/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.46/0.58  fof(f28,plain,(
% 1.46/0.58    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.46/0.58    inference(cnf_transformation,[],[f11])).
% 1.46/0.58  fof(f11,axiom,(
% 1.46/0.58    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.46/0.58  fof(f105,plain,(
% 1.46/0.58    ( ! [X8,X7] : (k1_setfam_1(k2_tarski(X7,X8)) = k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),X8)) )),
% 1.46/0.58    inference(forward_demodulation,[],[f104,f49])).
% 1.46/0.58  fof(f104,plain,(
% 1.46/0.58    ( ! [X8,X7] : (k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),k1_setfam_1(k2_tarski(X8,X8))) = k1_setfam_1(k2_tarski(X7,X8))) )),
% 1.46/0.58    inference(subsumption_resolution,[],[f103,f72])).
% 1.46/0.58  fof(f72,plain,(
% 1.46/0.58    ( ! [X0] : (k1_xboole_0 != k2_tarski(X0,X0)) )),
% 1.46/0.58    inference(subsumption_resolution,[],[f71,f68])).
% 1.46/0.58  fof(f68,plain,(
% 1.46/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.46/0.58    inference(superposition,[],[f65,f47])).
% 1.46/0.58  fof(f47,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.46/0.58    inference(definition_unfolding,[],[f32,f37])).
% 1.46/0.58  fof(f37,plain,(
% 1.46/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f7])).
% 1.46/0.58  fof(f7,axiom,(
% 1.46/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.46/0.58  fof(f32,plain,(
% 1.46/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.46/0.58    inference(cnf_transformation,[],[f6])).
% 1.46/0.58  fof(f6,axiom,(
% 1.46/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.46/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.46/0.58  fof(f65,plain,(
% 1.46/0.58    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.46/0.58    inference(equality_resolution,[],[f64])).
% 1.46/0.58  fof(f64,plain,(
% 1.46/0.58    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.46/0.58    inference(equality_resolution,[],[f58])).
% 1.46/0.58  fof(f58,plain,(
% 1.46/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.46/0.58    inference(definition_unfolding,[],[f40,f37])).
% 1.46/0.58  fof(f40,plain,(
% 1.46/0.58    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.46/0.58    inference(cnf_transformation,[],[f26])).
% 1.46/0.58  fof(f26,plain,(
% 1.46/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 1.46/0.58  % (11511)Refutation not found, incomplete strategy% (11511)------------------------------
% 1.46/0.58  % (11511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (11520)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.46/0.58  % (11511)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (11511)Memory used [KB]: 10618
% 1.46/0.58  % (11511)Time elapsed: 0.143 s
% 1.46/0.58  % (11511)------------------------------
% 1.46/0.58  % (11511)------------------------------
% 1.46/0.59  % (11503)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.59  % (11520)Refutation not found, incomplete strategy% (11520)------------------------------
% 1.46/0.59  % (11520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.59  fof(f25,plain,(
% 1.46/0.59    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 1.46/0.59    introduced(choice_axiom,[])).
% 1.46/0.59  fof(f24,plain,(
% 1.46/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.59    inference(rectify,[],[f23])).
% 1.46/0.59  fof(f23,plain,(
% 1.46/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.59    inference(flattening,[],[f22])).
% 1.46/0.59  fof(f22,plain,(
% 1.46/0.59    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.59    inference(nnf_transformation,[],[f18])).
% 1.46/0.59  fof(f18,plain,(
% 1.46/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.46/0.59    inference(ennf_transformation,[],[f3])).
% 1.46/0.59  fof(f3,axiom,(
% 1.46/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.46/0.59  fof(f71,plain,(
% 1.46/0.59    ( ! [X0] : (k1_xboole_0 != k2_tarski(X0,X0) | ~r2_hidden(X0,k2_tarski(X0,X0))) )),
% 1.46/0.59    inference(superposition,[],[f67,f30])).
% 1.46/0.59  fof(f30,plain,(
% 1.46/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.46/0.59    inference(cnf_transformation,[],[f14])).
% 1.46/0.59  fof(f14,plain,(
% 1.46/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.46/0.59    inference(rectify,[],[f2])).
% 1.46/0.59  fof(f2,axiom,(
% 1.46/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.46/0.59  fof(f67,plain,(
% 1.46/0.59    ( ! [X0,X1] : (k1_xboole_0 != k3_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.46/0.59    inference(resolution,[],[f51,f34])).
% 1.46/0.59  fof(f34,plain,(
% 1.46/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.46/0.59    inference(cnf_transformation,[],[f21])).
% 1.46/0.59  fof(f21,plain,(
% 1.46/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.46/0.59    inference(nnf_transformation,[],[f1])).
% 1.46/0.59  fof(f1,axiom,(
% 1.46/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.46/0.59  fof(f51,plain,(
% 1.46/0.59    ( ! [X0,X1] : (~r1_xboole_0(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.46/0.59    inference(definition_unfolding,[],[f36,f29])).
% 1.46/0.59  fof(f36,plain,(
% 1.46/0.59    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.46/0.59    inference(cnf_transformation,[],[f17])).
% 1.46/0.59  fof(f17,plain,(
% 1.46/0.59    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 1.46/0.59    inference(ennf_transformation,[],[f8])).
% 1.46/0.59  % (11508)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.59  fof(f8,axiom,(
% 1.46/0.59    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 1.46/0.59  fof(f103,plain,(
% 1.46/0.59    ( ! [X8,X7] : (k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),k1_setfam_1(k2_tarski(X8,X8))) = k1_setfam_1(k2_tarski(X7,X8)) | k1_xboole_0 = k2_tarski(X7,X7)) )),
% 1.46/0.59    inference(subsumption_resolution,[],[f98,f72])).
% 1.46/0.59  fof(f98,plain,(
% 1.46/0.59    ( ! [X8,X7] : (k3_xboole_0(k1_setfam_1(k2_tarski(X7,X7)),k1_setfam_1(k2_tarski(X8,X8))) = k1_setfam_1(k2_tarski(X7,X8)) | k1_xboole_0 = k2_tarski(X8,X8) | k1_xboole_0 = k2_tarski(X7,X7)) )),
% 1.46/0.59    inference(superposition,[],[f50,f74])).
% 1.46/0.59  fof(f74,plain,(
% 1.46/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 1.46/0.59    inference(superposition,[],[f73,f47])).
% 1.46/0.59  fof(f73,plain,(
% 1.46/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)))) )),
% 1.46/0.59    inference(superposition,[],[f48,f47])).
% 1.46/0.59  fof(f48,plain,(
% 1.46/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_enumset1(X0,X0,X1,X2),k2_tarski(X3,X3)))) )),
% 1.46/0.59    inference(definition_unfolding,[],[f38,f31,f37,f29])).
% 1.46/0.59  fof(f31,plain,(
% 1.46/0.59    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.46/0.59    inference(cnf_transformation,[],[f9])).
% 1.46/0.59  fof(f9,axiom,(
% 1.46/0.59    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.46/0.59  fof(f38,plain,(
% 1.46/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.46/0.59    inference(cnf_transformation,[],[f4])).
% 1.46/0.59  fof(f4,axiom,(
% 1.46/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.46/0.59  fof(f50,plain,(
% 1.46/0.59    ( ! [X0,X1] : (k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) = k1_setfam_1(k3_tarski(k2_tarski(X0,X1))) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.46/0.59    inference(definition_unfolding,[],[f35,f31])).
% 1.46/0.59  fof(f35,plain,(
% 1.46/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.46/0.59    inference(cnf_transformation,[],[f16])).
% 1.46/0.59  fof(f16,plain,(
% 1.46/0.59    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.46/0.59    inference(ennf_transformation,[],[f10])).
% 1.46/0.59  fof(f10,axiom,(
% 1.46/0.59    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.46/0.59  fof(f27,plain,(
% 1.46/0.59    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.46/0.59    inference(cnf_transformation,[],[f20])).
% 1.46/0.59  fof(f20,plain,(
% 1.46/0.59    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.46/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f19])).
% 1.46/0.59  fof(f19,plain,(
% 1.46/0.59    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 1.46/0.59    introduced(choice_axiom,[])).
% 1.46/0.59  fof(f15,plain,(
% 1.46/0.59    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.46/0.59    inference(ennf_transformation,[],[f13])).
% 1.46/0.59  fof(f13,negated_conjecture,(
% 1.46/0.59    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.46/0.59    inference(negated_conjecture,[],[f12])).
% 1.46/0.59  fof(f12,conjecture,(
% 1.46/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.46/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.46/0.59  % SZS output end Proof for theBenchmark
% 1.46/0.59  % (11497)------------------------------
% 1.46/0.59  % (11497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.59  % (11497)Termination reason: Refutation
% 1.46/0.59  
% 1.46/0.59  % (11497)Memory used [KB]: 10746
% 1.46/0.59  % (11503)Refutation not found, incomplete strategy% (11503)------------------------------
% 1.46/0.59  % (11503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.59  % (11497)Time elapsed: 0.135 s
% 1.46/0.59  % (11497)------------------------------
% 1.46/0.59  % (11497)------------------------------
% 1.46/0.59  % (11519)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.59  % (11503)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.59  
% 1.46/0.59  % (11503)Memory used [KB]: 10618
% 1.46/0.59  % (11503)Time elapsed: 0.150 s
% 1.46/0.59  % (11503)------------------------------
% 1.46/0.59  % (11503)------------------------------
% 1.46/0.59  % (11493)Success in time 0.216 s
%------------------------------------------------------------------------------
