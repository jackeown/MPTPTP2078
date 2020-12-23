%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:45 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 174 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  235 ( 553 expanded)
%              Number of equality atoms :  160 ( 391 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9187)Refutation not found, incomplete strategy% (9187)------------------------------
% (9187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9187)Termination reason: Refutation not found, incomplete strategy

% (9187)Memory used [KB]: 10618
% (9187)Time elapsed: 0.154 s
% (9187)------------------------------
% (9187)------------------------------
% (9199)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f175,plain,(
    $false ),
    inference(global_subsumption,[],[f82,f171])).

fof(f171,plain,(
    o_0_0_xboole_0 = sK0 ),
    inference(resolution,[],[f139,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f52,f44,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f139,plain,(
    ! [X0] : r1_tarski(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(global_subsumption,[],[f131,f137])).

fof(f137,plain,(
    ! [X0] :
      ( r2_hidden(sK1,sK0)
      | r1_tarski(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ) ),
    inference(superposition,[],[f57,f108])).

fof(f108,plain,(
    ! [X0] : sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) ),
    inference(global_subsumption,[],[f82,f106])).

fof(f106,plain,(
    ! [X0] :
      ( sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))
      | o_0_0_xboole_0 = sK0 ) ),
    inference(resolution,[],[f103,f85])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | sK1 = sK2(sK0,X0) ) ),
    inference(resolution,[],[f43,f57])).

fof(f43,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ! [X2] :
        ( sK1 = X2
        | ~ r2_hidden(X2,sK0) )
    & k1_xboole_0 != sK0
    & sK0 != k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( X1 = X2
            | ~ r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 )
   => ( ! [X2] :
          ( sK1 = X2
          | ~ r2_hidden(X2,sK0) )
      & k1_xboole_0 != sK0
      & sK0 != k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f131,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(global_subsumption,[],[f83,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f125])).

fof(f125,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK1 != sK1
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f88,f123])).

fof(f123,plain,(
    sK1 = sK3(sK1,sK1,sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK1,sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( sK0 != sK0
    | sK1 = sK3(sK1,sK1,sK1,sK0)
    | sK1 = sK3(sK1,sK1,sK1,sK0)
    | sK1 = sK3(sK1,sK1,sK1,sK0)
    | sK1 = sK3(sK1,sK1,sK1,sK0) ),
    inference(superposition,[],[f83,f105])).

fof(f105,plain,(
    ! [X4,X5,X3] :
      ( sK0 = k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5)
      | sK3(X3,X4,X5,sK0) = X5
      | sK3(X3,X4,X5,sK0) = X4
      | sK3(X3,X4,X5,sK0) = X3
      | sK1 = sK3(X3,X4,X5,sK0) ) ),
    inference(resolution,[],[f43,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK3(X0,X1,X2,X3),X3)
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f69,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f75,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

% (9194)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) = X2
      | sK3(X0,X1,X2,X3) = X1
      | sK3(X0,X1,X2,X3) = X0
      | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f39,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

% (9186)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2,X3),X3)
      | sK3(X0,X1,X2,X3) != X0
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3 ) ),
    inference(definition_unfolding,[],[f70,f79])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | sK3(X0,X1,X2,X3) != X0
      | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f41,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f79])).

fof(f49,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f41,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f42,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.55  % (9179)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (9178)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (9177)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (9176)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.47/0.56  % (9176)Refutation not found, incomplete strategy% (9176)------------------------------
% 1.47/0.56  % (9176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (9176)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (9176)Memory used [KB]: 1663
% 1.47/0.56  % (9176)Time elapsed: 0.109 s
% 1.47/0.56  % (9176)------------------------------
% 1.47/0.56  % (9176)------------------------------
% 1.47/0.56  % (9181)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.47/0.56  % (9195)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.57  % (9182)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.57  % (9187)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.57  % (9178)Refutation found. Thanks to Tanya!
% 1.47/0.57  % SZS status Theorem for theBenchmark
% 1.47/0.58  % (9198)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.47/0.58  % SZS output start Proof for theBenchmark
% 1.47/0.58  % (9187)Refutation not found, incomplete strategy% (9187)------------------------------
% 1.47/0.58  % (9187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.58  % (9187)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.58  
% 1.47/0.58  % (9187)Memory used [KB]: 10618
% 1.47/0.58  % (9187)Time elapsed: 0.154 s
% 1.47/0.58  % (9187)------------------------------
% 1.47/0.58  % (9187)------------------------------
% 1.47/0.58  % (9199)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.73/0.58  fof(f175,plain,(
% 1.73/0.58    $false),
% 1.73/0.58    inference(global_subsumption,[],[f82,f171])).
% 1.73/0.58  fof(f171,plain,(
% 1.73/0.58    o_0_0_xboole_0 = sK0),
% 1.73/0.58    inference(resolution,[],[f139,f85])).
% 1.73/0.58  fof(f85,plain,(
% 1.73/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | o_0_0_xboole_0 = X0) )),
% 1.73/0.58    inference(definition_unfolding,[],[f52,f44,f50])).
% 1.73/0.58  fof(f50,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.73/0.58    inference(cnf_transformation,[],[f6])).
% 1.73/0.58  fof(f6,axiom,(
% 1.73/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.73/0.58  fof(f44,plain,(
% 1.73/0.58    k1_xboole_0 = o_0_0_xboole_0),
% 1.73/0.58    inference(cnf_transformation,[],[f2])).
% 1.73/0.58  fof(f2,axiom,(
% 1.73/0.58    k1_xboole_0 = o_0_0_xboole_0),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.73/0.58  fof(f52,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 1.73/0.58    inference(cnf_transformation,[],[f23])).
% 1.73/0.58  fof(f23,plain,(
% 1.73/0.58    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 1.73/0.58    inference(ennf_transformation,[],[f9])).
% 1.73/0.58  fof(f9,axiom,(
% 1.73/0.58    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 1.73/0.58  fof(f139,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) )),
% 1.73/0.58    inference(global_subsumption,[],[f131,f137])).
% 1.73/0.58  fof(f137,plain,(
% 1.73/0.58    ( ! [X0] : (r2_hidden(sK1,sK0) | r1_tarski(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) )),
% 1.73/0.58    inference(superposition,[],[f57,f108])).
% 1.73/0.58  fof(f108,plain,(
% 1.73/0.58    ( ! [X0] : (sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0)))) )),
% 1.73/0.58    inference(global_subsumption,[],[f82,f106])).
% 1.73/0.58  fof(f106,plain,(
% 1.73/0.58    ( ! [X0] : (sK1 = sK2(sK0,k5_xboole_0(X0,k3_xboole_0(X0,sK0))) | o_0_0_xboole_0 = sK0) )),
% 1.73/0.58    inference(resolution,[],[f103,f85])).
% 1.73/0.58  fof(f103,plain,(
% 1.73/0.58    ( ! [X0] : (r1_tarski(sK0,X0) | sK1 = sK2(sK0,X0)) )),
% 1.73/0.58    inference(resolution,[],[f43,f57])).
% 1.73/0.58  fof(f43,plain,(
% 1.73/0.58    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 1.73/0.58    inference(cnf_transformation,[],[f28])).
% 1.73/0.58  fof(f28,plain,(
% 1.73/0.58    ! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1)),
% 1.73/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f27])).
% 1.73/0.58  fof(f27,plain,(
% 1.73/0.58    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0) => (! [X2] : (sK1 = X2 | ~r2_hidden(X2,sK0)) & k1_xboole_0 != sK0 & sK0 != k1_tarski(sK1))),
% 1.73/0.58    introduced(choice_axiom,[])).
% 1.73/0.58  fof(f21,plain,(
% 1.73/0.58    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.73/0.58    inference(ennf_transformation,[],[f20])).
% 1.73/0.58  fof(f20,negated_conjecture,(
% 1.73/0.58    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.73/0.58    inference(negated_conjecture,[],[f19])).
% 1.73/0.58  fof(f19,conjecture,(
% 1.73/0.58    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 1.73/0.58  fof(f57,plain,(
% 1.73/0.58    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f34])).
% 1.73/0.58  fof(f34,plain,(
% 1.73/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.73/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 1.73/0.58  fof(f33,plain,(
% 1.73/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.73/0.58    introduced(choice_axiom,[])).
% 1.73/0.58  fof(f32,plain,(
% 1.73/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.73/0.58    inference(rectify,[],[f31])).
% 1.73/0.58  fof(f31,plain,(
% 1.73/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.73/0.58    inference(nnf_transformation,[],[f24])).
% 1.73/0.58  fof(f24,plain,(
% 1.73/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.73/0.58    inference(ennf_transformation,[],[f3])).
% 1.73/0.58  fof(f3,axiom,(
% 1.73/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.73/0.58  fof(f131,plain,(
% 1.73/0.58    ~r2_hidden(sK1,sK0)),
% 1.73/0.58    inference(global_subsumption,[],[f83,f130])).
% 1.73/0.58  fof(f130,plain,(
% 1.73/0.58    ~r2_hidden(sK1,sK0) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.73/0.58    inference(trivial_inequality_removal,[],[f125])).
% 1.73/0.58  fof(f125,plain,(
% 1.73/0.58    ~r2_hidden(sK1,sK0) | sK1 != sK1 | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.73/0.58    inference(superposition,[],[f88,f123])).
% 1.73/0.58  fof(f123,plain,(
% 1.73/0.58    sK1 = sK3(sK1,sK1,sK1,sK0)),
% 1.73/0.58    inference(trivial_inequality_removal,[],[f122])).
% 1.73/0.58  fof(f122,plain,(
% 1.73/0.58    sK0 != sK0 | sK1 = sK3(sK1,sK1,sK1,sK0)),
% 1.73/0.58    inference(duplicate_literal_removal,[],[f121])).
% 1.73/0.58  fof(f121,plain,(
% 1.73/0.58    sK0 != sK0 | sK1 = sK3(sK1,sK1,sK1,sK0) | sK1 = sK3(sK1,sK1,sK1,sK0) | sK1 = sK3(sK1,sK1,sK1,sK0) | sK1 = sK3(sK1,sK1,sK1,sK0)),
% 1.73/0.58    inference(superposition,[],[f83,f105])).
% 1.73/0.58  fof(f105,plain,(
% 1.73/0.58    ( ! [X4,X5,X3] : (sK0 = k6_enumset1(X3,X3,X3,X3,X3,X3,X4,X5) | sK3(X3,X4,X5,sK0) = X5 | sK3(X3,X4,X5,sK0) = X4 | sK3(X3,X4,X5,sK0) = X3 | sK1 = sK3(X3,X4,X5,sK0)) )),
% 1.73/0.58    inference(resolution,[],[f43,f89])).
% 1.73/0.58  fof(f89,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (r2_hidden(sK3(X0,X1,X2,X3),X3) | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3) )),
% 1.73/0.58    inference(definition_unfolding,[],[f69,f79])).
% 1.73/0.58  fof(f79,plain,(
% 1.73/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f59,f78])).
% 1.73/0.58  fof(f78,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f64,f77])).
% 1.73/0.58  fof(f77,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f73,f76])).
% 1.73/0.58  fof(f76,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f74,f75])).
% 1.73/0.58  fof(f75,plain,(
% 1.73/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f17])).
% 1.73/0.58  fof(f17,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.73/0.58  fof(f74,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f16])).
% 1.73/0.58  fof(f16,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.73/0.58  fof(f73,plain,(
% 1.73/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f15])).
% 1.73/0.58  fof(f15,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.73/0.58  fof(f64,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f14])).
% 1.73/0.58  fof(f14,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.73/0.58  fof(f59,plain,(
% 1.73/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f13])).
% 1.73/0.58  % (9194)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.73/0.58  fof(f13,axiom,(
% 1.73/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.73/0.58  fof(f69,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f40])).
% 1.73/0.58  fof(f40,plain,(
% 1.73/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 1.73/0.58  fof(f39,plain,(
% 1.73/0.58    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.73/0.58    introduced(choice_axiom,[])).
% 1.73/0.58  fof(f38,plain,(
% 1.73/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.58    inference(rectify,[],[f37])).
% 1.73/0.58  fof(f37,plain,(
% 1.73/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.58    inference(flattening,[],[f36])).
% 1.73/0.58  fof(f36,plain,(
% 1.73/0.58    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.73/0.58    inference(nnf_transformation,[],[f26])).
% 1.73/0.58  fof(f26,plain,(
% 1.73/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.73/0.58    inference(ennf_transformation,[],[f10])).
% 1.73/0.58  % (9186)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.73/0.58  fof(f10,axiom,(
% 1.73/0.58    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.73/0.58  fof(f88,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X0,X1,X2,X3),X3) | sK3(X0,X1,X2,X3) != X0 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = X3) )),
% 1.73/0.58    inference(definition_unfolding,[],[f70,f79])).
% 1.73/0.58  fof(f70,plain,(
% 1.73/0.58    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | sK3(X0,X1,X2,X3) != X0 | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f40])).
% 1.73/0.58  fof(f83,plain,(
% 1.73/0.58    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.73/0.58    inference(definition_unfolding,[],[f41,f81])).
% 1.73/0.58  fof(f81,plain,(
% 1.73/0.58    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f45,f80])).
% 1.73/0.58  fof(f80,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.73/0.58    inference(definition_unfolding,[],[f49,f79])).
% 1.73/0.58  fof(f49,plain,(
% 1.73/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f12])).
% 1.73/0.58  fof(f12,axiom,(
% 1.73/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.73/0.58  fof(f45,plain,(
% 1.73/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.73/0.58    inference(cnf_transformation,[],[f11])).
% 1.73/0.58  fof(f11,axiom,(
% 1.73/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.73/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.73/0.58  fof(f41,plain,(
% 1.73/0.58    sK0 != k1_tarski(sK1)),
% 1.73/0.58    inference(cnf_transformation,[],[f28])).
% 1.73/0.58  fof(f82,plain,(
% 1.73/0.58    o_0_0_xboole_0 != sK0),
% 1.73/0.58    inference(definition_unfolding,[],[f42,f44])).
% 1.73/0.58  fof(f42,plain,(
% 1.73/0.58    k1_xboole_0 != sK0),
% 1.73/0.58    inference(cnf_transformation,[],[f28])).
% 1.73/0.58  % SZS output end Proof for theBenchmark
% 1.73/0.58  % (9178)------------------------------
% 1.73/0.58  % (9178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.58  % (9178)Termination reason: Refutation
% 1.73/0.58  
% 1.73/0.58  % (9178)Memory used [KB]: 10874
% 1.73/0.58  % (9178)Time elapsed: 0.152 s
% 1.73/0.58  % (9178)------------------------------
% 1.73/0.58  % (9178)------------------------------
% 1.73/0.58  % (9184)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.73/0.59  % (9189)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.73/0.59  % (9193)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.73/0.59  % (9175)Success in time 0.224 s
%------------------------------------------------------------------------------
