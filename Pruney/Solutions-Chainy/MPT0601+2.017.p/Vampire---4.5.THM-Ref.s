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
% DateTime   : Thu Dec  3 12:51:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 277 expanded)
%              Number of leaves         :   21 (  76 expanded)
%              Depth                    :   17
%              Number of atoms          :  234 ( 707 expanded)
%              Number of equality atoms :   82 ( 313 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(subsumption_resolution,[],[f269,f180])).

fof(f180,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f133,f178])).

fof(f178,plain,(
    ! [X2] : r1_xboole_0(k1_xboole_0,X2) ),
    inference(subsumption_resolution,[],[f177,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

% (16806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f177,plain,(
    ! [X2] :
      ( r1_xboole_0(k1_xboole_0,X2)
      | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK5(k1_xboole_0,X2),sK5(k1_xboole_0,X2))) ) ),
    inference(resolution,[],[f175,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(backward_demodulation,[],[f85,f89])).

fof(f89,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f77,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f61,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f75,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f75,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f175,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f171,f53])).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(sK5(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k1_xboole_0))
      | r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f87,f53])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f129,f53])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0))
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f86,f53])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f73])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f269,plain,(
    r2_hidden(sK4(sK1,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f268,f258])).

fof(f258,plain,(
    k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f256,f98])).

fof(f98,plain,(
    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0) ),
    inference(resolution,[],[f58,f50])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

fof(f256,plain,
    ( k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_xboole_0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f255,f148])).

fof(f148,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_tarski(X0,X0)) ),
    inference(resolution,[],[f95,f50])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) ) ),
    inference(backward_demodulation,[],[f82,f89])).

% (16824)Refutation not found, incomplete strategy% (16824)------------------------------
% (16824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16824)Termination reason: Refutation not found, incomplete strategy

% (16824)Memory used [KB]: 10746
% (16824)Time elapsed: 0.090 s
% (16824)------------------------------
% (16824)------------------------------
fof(f82,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1))))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f81])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f255,plain,
    ( k9_relat_1(sK1,k1_xboole_0) = k9_relat_1(sK1,k2_tarski(sK0,sK0))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f253,f100])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f74,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f253,plain,
    ( k9_relat_1(sK1,k2_tarski(sK0,sK0)) = k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1)))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f240,f137])).

fof(f137,plain,
    ( k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(resolution,[],[f94,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 ) ),
    inference(backward_demodulation,[],[f84,f89])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f62,f81])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f240,plain,(
    ! [X0] : k9_relat_1(sK1,X0) = k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0))) ),
    inference(resolution,[],[f88,f50])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f71,f73])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

fof(f268,plain,(
    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f265,f50])).

fof(f265,plain,
    ( r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f259,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f259,plain,(
    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) ),
    inference(subsumption_resolution,[],[f146,f258])).

fof(f146,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1) ),
    inference(resolution,[],[f92,f51])).

fof(f51,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f45,f44,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK2(X0,X1),X3),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (16807)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (16804)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16830)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (16811)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (16814)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (16807)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (16820)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (16804)Refutation not found, incomplete strategy% (16804)------------------------------
% 0.20/0.52  % (16804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16804)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16804)Memory used [KB]: 10746
% 0.20/0.52  % (16804)Time elapsed: 0.114 s
% 0.20/0.52  % (16804)------------------------------
% 0.20/0.52  % (16804)------------------------------
% 0.20/0.53  % (16824)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(subsumption_resolution,[],[f269,f180])).
% 0.20/0.53  fof(f180,plain,(
% 0.20/0.53    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f133,f178])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f177,f53])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.20/0.53  % (16806)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  fof(f177,plain,(
% 0.20/0.53    ( ! [X2] : (r1_xboole_0(k1_xboole_0,X2) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK5(k1_xboole_0,X2),sK5(k1_xboole_0,X2)))) )),
% 0.20/0.53    inference(resolution,[],[f175,f93])).
% 0.20/0.53  fof(f93,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 0.20/0.53    inference(backward_demodulation,[],[f85,f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.20/0.53    inference(definition_unfolding,[],[f77,f79])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 1.32/0.53  fof(f11,axiom,(
% 1.32/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 1.32/0.53  fof(f77,plain,(
% 1.32/0.53    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.32/0.53    inference(rectify,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.32/0.53  fof(f85,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) != X0) )),
% 1.32/0.53    inference(definition_unfolding,[],[f61,f81])).
% 1.32/0.53  fof(f81,plain,(
% 1.32/0.53    ( ! [X0] : (k1_tarski(X0) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X0,X0)))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f75,f80])).
% 1.32/0.53  fof(f80,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k2_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f76,f79])).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.32/0.53  fof(f75,plain,(
% 1.32/0.53    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f40])).
% 1.32/0.53  fof(f40,plain,(
% 1.32/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.32/0.53    inference(nnf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.32/0.53  fof(f175,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,X0),k1_xboole_0) | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f171,f53])).
% 1.32/0.53  fof(f171,plain,(
% 1.32/0.53    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,k1_xboole_0)) | r1_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f87,f53])).
% 1.32/0.53  fof(f87,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f67,f73])).
% 1.32/0.53  fof(f73,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.32/0.53  fof(f67,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f48])).
% 1.32/0.53  fof(f48,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f47])).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK5(X0,X1),k3_xboole_0(X0,X1)))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(ennf_transformation,[],[f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    inference(rectify,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.32/0.53  fof(f133,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f129,f53])).
% 1.32/0.53  fof(f129,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f86,f53])).
% 1.32/0.53  fof(f86,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f68,f73])).
% 1.32/0.53  fof(f68,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f48])).
% 1.32/0.53  fof(f269,plain,(
% 1.32/0.53    r2_hidden(sK4(sK1,sK0),k1_xboole_0)),
% 1.32/0.53    inference(forward_demodulation,[],[f268,f258])).
% 1.32/0.53  fof(f258,plain,(
% 1.32/0.53    k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(duplicate_literal_removal,[],[f257])).
% 1.32/0.53  fof(f257,plain,(
% 1.32/0.53    k1_xboole_0 = k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(forward_demodulation,[],[f256,f98])).
% 1.32/0.53  fof(f98,plain,(
% 1.32/0.53    k1_xboole_0 = k9_relat_1(sK1,k1_xboole_0)),
% 1.32/0.53    inference(resolution,[],[f58,f50])).
% 1.32/0.53  fof(f50,plain,(
% 1.32/0.53    v1_relat_1(sK1)),
% 1.32/0.53    inference(cnf_transformation,[],[f38])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).
% 1.32/0.53  fof(f37,plain,(
% 1.32/0.53    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 1.32/0.53    inference(flattening,[],[f35])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f26])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,negated_conjecture,(
% 1.32/0.53    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.32/0.53    inference(negated_conjecture,[],[f22])).
% 1.32/0.53  fof(f22,conjecture,(
% 1.32/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).
% 1.32/0.53  fof(f256,plain,(
% 1.32/0.53    k11_relat_1(sK1,sK0) = k9_relat_1(sK1,k1_xboole_0) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(forward_demodulation,[],[f255,f148])).
% 1.32/0.53  fof(f148,plain,(
% 1.32/0.53    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_tarski(X0,X0))) )),
% 1.32/0.53    inference(resolution,[],[f95,f50])).
% 1.32/0.53  fof(f95,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))) )),
% 1.32/0.53    inference(backward_demodulation,[],[f82,f89])).
% 1.32/0.53  % (16824)Refutation not found, incomplete strategy% (16824)------------------------------
% 1.32/0.53  % (16824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (16824)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (16824)Memory used [KB]: 10746
% 1.32/0.53  % (16824)Time elapsed: 0.090 s
% 1.32/0.53  % (16824)------------------------------
% 1.32/0.53  % (16824)------------------------------
% 1.32/0.53  fof(f82,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) | ~v1_relat_1(X0)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f56,f81])).
% 1.32/0.53  fof(f56,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f13])).
% 1.32/0.53  fof(f13,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.32/0.53  fof(f255,plain,(
% 1.32/0.53    k9_relat_1(sK1,k1_xboole_0) = k9_relat_1(sK1,k2_tarski(sK0,sK0)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(forward_demodulation,[],[f253,f100])).
% 1.32/0.53  fof(f100,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.32/0.53    inference(resolution,[],[f74,f60])).
% 1.32/0.53  fof(f60,plain,(
% 1.32/0.53    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f30])).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.32/0.53  fof(f74,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).
% 1.32/0.53  fof(f253,plain,(
% 1.32/0.53    k9_relat_1(sK1,k2_tarski(sK0,sK0)) = k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k1_relat_1(sK1))) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(superposition,[],[f240,f137])).
% 1.32/0.53  fof(f137,plain,(
% 1.32/0.53    k1_relat_1(sK1) = k4_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(resolution,[],[f94,f52])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    ~r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f38])).
% 1.32/0.53  fof(f94,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) = X0) )),
% 1.32/0.53    inference(backward_demodulation,[],[f84,f89])).
% 1.32/0.53  fof(f84,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X1,X1)))) = X0 | r2_hidden(X1,X0)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f62,f81])).
% 1.32/0.53  fof(f62,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f40])).
% 1.32/0.53  fof(f240,plain,(
% 1.32/0.53    ( ! [X0] : (k9_relat_1(sK1,X0) = k9_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X0)))) )),
% 1.32/0.53    inference(resolution,[],[f88,f50])).
% 1.32/0.53  fof(f88,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) )),
% 1.32/0.53    inference(definition_unfolding,[],[f71,f73])).
% 1.32/0.53  fof(f71,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f33])).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,axiom,(
% 1.32/0.53    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).
% 1.32/0.53  fof(f268,plain,(
% 1.32/0.53    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.32/0.53    inference(subsumption_resolution,[],[f265,f50])).
% 1.32/0.53  fof(f265,plain,(
% 1.32/0.53    r2_hidden(sK4(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1)),
% 1.32/0.53    inference(resolution,[],[f259,f54])).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f39])).
% 1.32/0.53  fof(f39,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 1.32/0.53    inference(nnf_transformation,[],[f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.32/0.53    inference(ennf_transformation,[],[f19])).
% 1.32/0.53  fof(f19,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.32/0.53  fof(f259,plain,(
% 1.32/0.53    r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)),
% 1.32/0.53    inference(subsumption_resolution,[],[f146,f258])).
% 1.32/0.53  fof(f146,plain,(
% 1.32/0.53    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(k4_tarski(sK0,sK4(sK1,sK0)),sK1)),
% 1.32/0.53    inference(resolution,[],[f92,f51])).
% 1.32/0.53  fof(f51,plain,(
% 1.32/0.53    r2_hidden(sK0,k1_relat_1(sK1)) | k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f38])).
% 1.32/0.53  fof(f92,plain,(
% 1.32/0.53    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0)) )),
% 1.32/0.53    inference(equality_resolution,[],[f63])).
% 1.32/0.53  fof(f63,plain,(
% 1.32/0.53    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 1.32/0.53    inference(cnf_transformation,[],[f46])).
% 1.32/0.53  fof(f46,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.32/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f42,f45,f44,f43])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK2(X0,X1),X3),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK2(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK4(X0,X5)),X0))),
% 1.32/0.53    introduced(choice_axiom,[])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 1.32/0.53    inference(rectify,[],[f41])).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 1.32/0.53    inference(nnf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,axiom,(
% 1.32/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (16807)------------------------------
% 1.32/0.53  % (16807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (16807)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (16807)Memory used [KB]: 6396
% 1.32/0.53  % (16807)Time elapsed: 0.109 s
% 1.32/0.53  % (16807)------------------------------
% 1.32/0.53  % (16807)------------------------------
% 1.32/0.53  % (16801)Success in time 0.171 s
%------------------------------------------------------------------------------
