%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   63 (  65 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :  182 ( 192 expanded)
%              Number of equality atoms :   93 (  99 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(subsumption_resolution,[],[f86,f167])).

fof(f167,plain,(
    ! [X0] : k4_xboole_0(X0,k1_tarski(X0)) = X0 ),
    inference(resolution,[],[f166,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_tarski(X3),X2)
      | k4_xboole_0(X2,k1_tarski(X3)) = X2 ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f166,plain,(
    ! [X9] : ~ r1_tarski(k1_tarski(X9),X9) ),
    inference(resolution,[],[f157,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f157,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f156,f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X7,X5,X4,X3,X2,X1,X0)
        | ( X5 != X7
          & X4 != X7
          & X3 != X7
          & X2 != X7
          & X1 != X7
          & X0 != X7 ) )
      & ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7
        | ~ sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X7,X5,X4,X3,X2,X1,X0] :
      ( sP0(X7,X5,X4,X3,X2,X1,X0)
    <=> ( X5 = X7
        | X4 = X7
        | X3 = X7
        | X2 = X7
        | X1 = X7
        | X0 = X7 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f156,plain,(
    ! [X26,X25] :
      ( ~ sP0(X25,X26,X26,X26,X26,X26,X26)
      | r2_hidden(X25,k1_tarski(X26)) ) ),
    inference(resolution,[],[f56,f93])).

fof(f93,plain,(
    ! [X0] : sP1(X0,X0,X0,X0,X0,X0,k1_tarski(X0)) ),
    inference(superposition,[],[f92,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f92,plain,(
    ! [X0,X1] : sP1(X0,X0,X0,X0,X0,X1,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f91,f43])).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X1] : sP1(X0,X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f90,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : sP1(X0,X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3)) ),
    inference(superposition,[],[f89,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] : sP1(X0,X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4)) ),
    inference(superposition,[],[f74,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(definition_folding,[],[f21,f23,f22])).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6)
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> sP0(X7,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4,X5,X6)
      | ~ sP0(X8,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X8,X6) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X7,X6) )
          & ( sP0(X7,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X7,X6) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ~ sP0(X8,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X8,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X8,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6)
        | ? [X7] :
            ( ( ~ sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ~ sP0(X7,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X7,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X7,X6) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f86,plain,(
    sK2 != k4_xboole_0(sK2,k1_tarski(sK2)) ),
    inference(superposition,[],[f75,f79])).

fof(f79,plain,(
    ! [X0] : k4_xboole_0(X0,k1_tarski(X0)) = k4_xboole_0(k1_ordinal1(X0),k1_tarski(X0)) ),
    inference(superposition,[],[f45,f39])).

fof(f39,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f75,plain,(
    sK2 != k4_xboole_0(k1_ordinal1(sK2),k1_tarski(sK2)) ),
    inference(superposition,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f37,plain,(
    sK2 != k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    sK2 != k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).

fof(f25,plain,
    ( ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0
   => sK2 != k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:01:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (3080)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (3072)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (3080)Refutation not found, incomplete strategy% (3080)------------------------------
% 0.21/0.50  % (3080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3080)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3080)Memory used [KB]: 1791
% 0.21/0.50  % (3080)Time elapsed: 0.059 s
% 0.21/0.50  % (3080)------------------------------
% 0.21/0.50  % (3080)------------------------------
% 0.21/0.51  % (3064)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (3063)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (3064)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_tarski(X0)) = X0) )),
% 0.21/0.51    inference(resolution,[],[f166,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X2,X3] : (r1_tarski(k1_tarski(X3),X2) | k4_xboole_0(X2,k1_tarski(X3)) = X2) )),
% 0.21/0.51    inference(resolution,[],[f49,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ( ! [X9] : (~r1_tarski(k1_tarski(X9),X9)) )),
% 0.21/0.51    inference(resolution,[],[f157,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,axiom,(
% 0.21/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.21/0.51    inference(resolution,[],[f156,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6)) )),
% 0.21/0.51    inference(equality_resolution,[],[f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 0.21/0.51    inference(rectify,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X7,X5,X4,X3,X2,X1,X0] : ((sP0(X7,X5,X4,X3,X2,X1,X0) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X7,X5,X4,X3,X2,X1,X0] : (sP0(X7,X5,X4,X3,X2,X1,X0) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X26,X25] : (~sP0(X25,X26,X26,X26,X26,X26,X26) | r2_hidden(X25,k1_tarski(X26))) )),
% 0.21/0.51    inference(resolution,[],[f56,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0] : (sP1(X0,X0,X0,X0,X0,X0,k1_tarski(X0))) )),
% 0.21/0.51    inference(superposition,[],[f92,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.27/0.52  fof(f92,plain,(
% 1.27/0.52    ( ! [X0,X1] : (sP1(X0,X0,X0,X0,X0,X1,k2_tarski(X0,X1))) )),
% 1.27/0.52    inference(superposition,[],[f91,f43])).
% 1.27/0.52  fof(f43,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f4])).
% 1.27/0.52  fof(f4,axiom,(
% 1.27/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.27/0.52  fof(f91,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (sP1(X0,X0,X0,X0,X1,X2,k1_enumset1(X0,X1,X2))) )),
% 1.27/0.52    inference(superposition,[],[f90,f51])).
% 1.27/0.52  fof(f51,plain,(
% 1.27/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f5])).
% 1.27/0.52  fof(f5,axiom,(
% 1.27/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.27/0.52  fof(f90,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (sP1(X0,X0,X0,X1,X2,X3,k2_enumset1(X0,X1,X2,X3))) )),
% 1.27/0.52    inference(superposition,[],[f89,f52])).
% 1.27/0.52  fof(f52,plain,(
% 1.27/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f6])).
% 1.27/0.52  fof(f6,axiom,(
% 1.27/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.27/0.52  fof(f89,plain,(
% 1.27/0.52    ( ! [X4,X2,X0,X3,X1] : (sP1(X0,X0,X1,X2,X3,X4,k3_enumset1(X0,X1,X2,X3,X4))) )),
% 1.27/0.52    inference(superposition,[],[f74,f53])).
% 1.27/0.52  fof(f53,plain,(
% 1.27/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f7])).
% 1.27/0.52  fof(f7,axiom,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.27/0.52  fof(f74,plain,(
% 1.27/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,k4_enumset1(X0,X1,X2,X3,X4,X5))) )),
% 1.27/0.52    inference(equality_resolution,[],[f66])).
% 1.27/0.52  fof(f66,plain,(
% 1.27/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.27/0.52    inference(cnf_transformation,[],[f36])).
% 1.27/0.52  fof(f36,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) & (sP1(X0,X1,X2,X3,X4,X5,X6) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.27/0.52    inference(nnf_transformation,[],[f24])).
% 1.27/0.52  fof(f24,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> sP1(X0,X1,X2,X3,X4,X5,X6))),
% 1.27/0.52    inference(definition_folding,[],[f21,f23,f22])).
% 1.27/0.52  fof(f23,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : (sP1(X0,X1,X2,X3,X4,X5,X6) <=> ! [X7] : (r2_hidden(X7,X6) <=> sP0(X7,X5,X4,X3,X2,X1,X0)))),
% 1.27/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.27/0.52  fof(f21,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.27/0.52    inference(ennf_transformation,[],[f12])).
% 1.27/0.52  fof(f12,axiom,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 1.27/0.52  fof(f56,plain,(
% 1.27/0.52    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (~sP1(X0,X1,X2,X3,X4,X5,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0) | r2_hidden(X8,X6)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f32])).
% 1.27/0.52  fof(f32,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 1.27/0.52  fof(f31,plain,(
% 1.27/0.52    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6),X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f30,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | ~sP0(X8,X5,X4,X3,X2,X1,X0)) & (sP0(X8,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X8,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.27/0.52    inference(rectify,[],[f29])).
% 1.27/0.52  fof(f29,plain,(
% 1.27/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP1(X0,X1,X2,X3,X4,X5,X6) | ? [X7] : ((~sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | ~sP0(X7,X5,X4,X3,X2,X1,X0)) & (sP0(X7,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X7,X6))) | ~sP1(X0,X1,X2,X3,X4,X5,X6)))),
% 1.27/0.52    inference(nnf_transformation,[],[f23])).
% 1.27/0.52  fof(f86,plain,(
% 1.27/0.52    sK2 != k4_xboole_0(sK2,k1_tarski(sK2))),
% 1.27/0.52    inference(superposition,[],[f75,f79])).
% 1.27/0.52  fof(f79,plain,(
% 1.27/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_tarski(X0)) = k4_xboole_0(k1_ordinal1(X0),k1_tarski(X0))) )),
% 1.27/0.52    inference(superposition,[],[f45,f39])).
% 1.27/0.52  fof(f39,plain,(
% 1.27/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.27/0.52    inference(cnf_transformation,[],[f15])).
% 1.27/0.52  fof(f15,axiom,(
% 1.27/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.27/0.52  fof(f45,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f2])).
% 1.27/0.52  fof(f2,axiom,(
% 1.27/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.27/0.52  fof(f75,plain,(
% 1.27/0.52    sK2 != k4_xboole_0(k1_ordinal1(sK2),k1_tarski(sK2))),
% 1.27/0.52    inference(superposition,[],[f37,f40])).
% 1.27/0.52  fof(f40,plain,(
% 1.27/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.27/0.52    inference(cnf_transformation,[],[f13])).
% 1.27/0.52  fof(f13,axiom,(
% 1.27/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.27/0.52  fof(f37,plain,(
% 1.27/0.52    sK2 != k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2))),
% 1.27/0.52    inference(cnf_transformation,[],[f26])).
% 1.27/0.52  fof(f26,plain,(
% 1.27/0.52    sK2 != k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2))),
% 1.27/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f25])).
% 1.27/0.52  fof(f25,plain,(
% 1.27/0.52    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0 => sK2 != k6_subset_1(k1_ordinal1(sK2),k1_tarski(sK2))),
% 1.27/0.52    introduced(choice_axiom,[])).
% 1.27/0.52  fof(f19,plain,(
% 1.27/0.52    ? [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) != X0),
% 1.27/0.52    inference(ennf_transformation,[],[f18])).
% 1.27/0.52  fof(f18,negated_conjecture,(
% 1.27/0.52    ~! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 1.27/0.52    inference(negated_conjecture,[],[f17])).
% 1.27/0.52  fof(f17,conjecture,(
% 1.27/0.52    ! [X0] : k6_subset_1(k1_ordinal1(X0),k1_tarski(X0)) = X0),
% 1.27/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_ordinal1)).
% 1.27/0.52  % SZS output end Proof for theBenchmark
% 1.27/0.52  % (3064)------------------------------
% 1.27/0.52  % (3064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (3064)Termination reason: Refutation
% 1.27/0.52  
% 1.27/0.52  % (3064)Memory used [KB]: 6396
% 1.27/0.52  % (3064)Time elapsed: 0.077 s
% 1.27/0.52  % (3064)------------------------------
% 1.27/0.52  % (3064)------------------------------
% 1.27/0.52  % (3056)Success in time 0.159 s
%------------------------------------------------------------------------------
