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
% DateTime   : Thu Dec  3 12:48:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 112 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  158 ( 215 expanded)
%              Number of equality atoms :   55 (  94 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (29849)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f78])).

% (29847)Refutation not found, incomplete strategy% (29847)------------------------------
% (29847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29847)Termination reason: Refutation not found, incomplete strategy

% (29847)Memory used [KB]: 10618
% (29847)Time elapsed: 0.146 s
% (29847)------------------------------
% (29847)------------------------------
fof(f78,plain,(
    o_0_0_xboole_0 != k3_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f43,f44,f44])).

fof(f44,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f43,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f16])).

fof(f16,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f133,plain,(
    o_0_0_xboole_0 = k3_relat_1(o_0_0_xboole_0) ),
    inference(forward_demodulation,[],[f132,f82])).

fof(f82,plain,(
    ! [X0] : k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f48,f77,f44])).

fof(f77,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f76])).

% (29845)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (29846)Refutation not found, incomplete strategy% (29846)------------------------------
% (29846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29846)Termination reason: Refutation not found, incomplete strategy

% (29846)Memory used [KB]: 10618
% (29846)Time elapsed: 0.145 s
% (29846)------------------------------
% (29846)------------------------------
fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

% (29839)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f132,plain,(
    k3_relat_1(o_0_0_xboole_0) = k3_tarski(k5_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)) ),
    inference(forward_demodulation,[],[f131,f79])).

fof(f79,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f46,f44,f44])).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f131,plain,(
    k3_relat_1(o_0_0_xboole_0) = k3_tarski(k5_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k2_relat_1(o_0_0_xboole_0))) ),
    inference(subsumption_resolution,[],[f128,f115])).

fof(f115,plain,(
    v1_relat_1(o_0_0_xboole_0) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | v1_relat_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (29839)Refutation not found, incomplete strategy% (29839)------------------------------
% (29839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29839)Termination reason: Refutation not found, incomplete strategy

% (29839)Memory used [KB]: 10618
% (29839)Time elapsed: 0.138 s
% (29839)------------------------------
% (29839)------------------------------
% (29841)Refutation not found, incomplete strategy% (29841)------------------------------
% (29841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29841)Termination reason: Refutation not found, incomplete strategy

% (29841)Memory used [KB]: 6140
% (29841)Time elapsed: 0.138 s
% (29841)------------------------------
% (29841)------------------------------
fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(o_0_0_xboole_0),X0)
      | v1_relat_1(o_0_0_xboole_0) ) ),
    inference(resolution,[],[f108,f50])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,o_0_0_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f105,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f39])).

% (29838)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f39,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f105,plain,(
    ! [X4,X3] :
      ( sP1(o_0_0_xboole_0,X3,X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f61,f89])).

fof(f89,plain,(
    ! [X0] : sP2(X0,o_0_0_xboole_0,X0) ),
    inference(superposition,[],[f85,f81])).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f47,f44])).

fof(f47,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f85,plain,(
    ! [X0,X1] : sP2(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f24,f23])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP1(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP1(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP1(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f128,plain,
    ( k3_relat_1(o_0_0_xboole_0) = k3_tarski(k5_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k2_relat_1(o_0_0_xboole_0)))
    | ~ v1_relat_1(o_0_0_xboole_0) ),
    inference(superposition,[],[f83,f80])).

fof(f80,plain,(
    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f45,f44,f44])).

fof(f45,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

% (29864)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f83,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f49,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:17:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (29850)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (29840)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (29860)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (29851)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (29860)Refutation not found, incomplete strategy% (29860)------------------------------
% 0.21/0.54  % (29860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29860)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29860)Memory used [KB]: 1663
% 0.21/0.54  % (29860)Time elapsed: 0.045 s
% 0.21/0.54  % (29860)------------------------------
% 0.21/0.54  % (29860)------------------------------
% 0.21/0.54  % (29841)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (29837)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (29837)Refutation not found, incomplete strategy% (29837)------------------------------
% 0.21/0.55  % (29837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29837)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29837)Memory used [KB]: 1663
% 0.21/0.55  % (29837)Time elapsed: 0.133 s
% 0.21/0.55  % (29837)------------------------------
% 0.21/0.55  % (29837)------------------------------
% 0.21/0.55  % (29863)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (29866)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (29858)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (29866)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % (29858)Refutation not found, incomplete strategy% (29858)------------------------------
% 0.21/0.56  % (29858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29858)Memory used [KB]: 1663
% 0.21/0.56  % (29858)Time elapsed: 0.134 s
% 0.21/0.56  % (29858)------------------------------
% 0.21/0.56  % (29858)------------------------------
% 0.21/0.56  % (29847)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (29846)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  % (29849)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f134,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(subsumption_resolution,[],[f133,f78])).
% 0.21/0.56  % (29847)Refutation not found, incomplete strategy% (29847)------------------------------
% 0.21/0.56  % (29847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29847)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29847)Memory used [KB]: 10618
% 0.21/0.56  % (29847)Time elapsed: 0.146 s
% 0.21/0.56  % (29847)------------------------------
% 0.21/0.56  % (29847)------------------------------
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    o_0_0_xboole_0 != k3_relat_1(o_0_0_xboole_0)),
% 0.21/0.56    inference(definition_unfolding,[],[f43,f44,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.56    inference(cnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    k1_xboole_0 = o_0_0_xboole_0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.56  fof(f16,negated_conjecture,(
% 0.21/0.56    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(negated_conjecture,[],[f15])).
% 0.21/0.56  fof(f15,conjecture,(
% 0.21/0.56    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    o_0_0_xboole_0 = k3_relat_1(o_0_0_xboole_0)),
% 0.21/0.56    inference(forward_demodulation,[],[f132,f82])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0] : (k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,o_0_0_xboole_0)) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f48,f77,f44])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f52,f76])).
% 0.21/0.56  % (29845)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (29846)Refutation not found, incomplete strategy% (29846)------------------------------
% 0.21/0.56  % (29846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29846)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29846)Memory used [KB]: 10618
% 0.21/0.56  % (29846)Time elapsed: 0.145 s
% 0.21/0.56  % (29846)------------------------------
% 0.21/0.56  % (29846)------------------------------
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f53,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f60,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f70,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f71,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f8])).
% 0.21/0.56  % (29839)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    k3_relat_1(o_0_0_xboole_0) = k3_tarski(k5_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0))),
% 0.21/0.56    inference(forward_demodulation,[],[f131,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0)),
% 0.21/0.56    inference(definition_unfolding,[],[f46,f44,f44])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    k3_relat_1(o_0_0_xboole_0) = k3_tarski(k5_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k2_relat_1(o_0_0_xboole_0)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f128,f115])).
% 0.21/0.56  fof(f115,plain,(
% 0.21/0.56    v1_relat_1(o_0_0_xboole_0)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    v1_relat_1(o_0_0_xboole_0) | v1_relat_1(o_0_0_xboole_0)),
% 0.21/0.56    inference(resolution,[],[f111,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  % (29839)Refutation not found, incomplete strategy% (29839)------------------------------
% 0.21/0.56  % (29839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29839)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29839)Memory used [KB]: 10618
% 0.21/0.56  % (29839)Time elapsed: 0.138 s
% 0.21/0.56  % (29839)------------------------------
% 0.21/0.56  % (29839)------------------------------
% 0.21/0.56  % (29841)Refutation not found, incomplete strategy% (29841)------------------------------
% 0.21/0.56  % (29841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29841)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29841)Memory used [KB]: 6140
% 0.21/0.56  % (29841)Time elapsed: 0.138 s
% 0.21/0.56  % (29841)------------------------------
% 0.21/0.56  % (29841)------------------------------
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.21/0.56    inference(unused_predicate_definition_removal,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(sK3(o_0_0_xboole_0),X0) | v1_relat_1(o_0_0_xboole_0)) )),
% 0.21/0.56    inference(resolution,[],[f108,f50])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X0,o_0_0_xboole_0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(resolution,[],[f105,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.56    inference(flattening,[],[f39])).
% 0.21/0.56  % (29838)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X4,X3] : (sP1(o_0_0_xboole_0,X3,X4) | ~r2_hidden(X3,X4)) )),
% 0.21/0.56    inference(resolution,[],[f61,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0] : (sP2(X0,o_0_0_xboole_0,X0)) )),
% 0.21/0.56    inference(superposition,[],[f85,f81])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f47,f44])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP2(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.21/0.57    inference(definition_folding,[],[f2,f24,f23])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | sP1(X1,X4,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f36,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.57    inference(nnf_transformation,[],[f24])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    k3_relat_1(o_0_0_xboole_0) = k3_tarski(k5_enumset1(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0,k2_relat_1(o_0_0_xboole_0))) | ~v1_relat_1(o_0_0_xboole_0)),
% 0.21/0.57    inference(superposition,[],[f83,f80])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    o_0_0_xboole_0 = k1_relat_1(o_0_0_xboole_0)),
% 0.21/0.57    inference(definition_unfolding,[],[f45,f44,f44])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f14])).
% 0.21/0.57  % (29864)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k5_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(definition_unfolding,[],[f49,f77])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (29866)------------------------------
% 0.21/0.57  % (29866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (29866)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (29866)Memory used [KB]: 1791
% 0.21/0.57  % (29866)Time elapsed: 0.141 s
% 0.21/0.57  % (29866)------------------------------
% 0.21/0.57  % (29866)------------------------------
% 0.21/0.57  % (29862)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (29836)Success in time 0.204 s
%------------------------------------------------------------------------------
