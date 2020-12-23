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
% DateTime   : Thu Dec  3 12:39:59 EST 2020

% Result     : Theorem 2.41s
% Output     : Refutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 136 expanded)
%              Number of leaves         :   16 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  203 ( 292 expanded)
%              Number of equality atoms :  115 ( 175 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1440,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1434,f38])).

fof(f38,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r2_hidden(sK2,sK1)
    & k1_tarski(sK2) = k3_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) )
   => ( ~ r2_hidden(sK2,sK1)
      & k1_tarski(sK2) = k3_xboole_0(sK1,k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
       => r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f1434,plain,(
    r2_hidden(sK2,sK1) ),
    inference(superposition,[],[f110,f1423])).

fof(f1423,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(forward_demodulation,[],[f1400,f363])).

fof(f363,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f342,f334])).

fof(f334,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f310,f191])).

fof(f191,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f190,f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f190,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f185,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f185,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f46,f39])).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f310,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f49,f39])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f342,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f334,f43])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1400,plain,(
    k2_xboole_0(sK1,k1_tarski(sK2)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK2)),k1_tarski(sK2)) ),
    inference(superposition,[],[f347,f37])).

fof(f37,plain,(
    k1_tarski(sK2) = k3_xboole_0(sK1,k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f347,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11)) ),
    inference(superposition,[],[f334,f46])).

fof(f110,plain,(
    ! [X12,X11] : r2_hidden(X11,k2_xboole_0(X12,k1_tarski(X11))) ),
    inference(forward_demodulation,[],[f107,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f107,plain,(
    ! [X12,X11] : r2_hidden(X11,k3_tarski(k2_tarski(X12,k1_tarski(X11)))) ),
    inference(resolution,[],[f80,f90])).

fof(f90,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f89,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f89,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f88,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f47,f76])).

fof(f76,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(forward_demodulation,[],[f74,f42])).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f44,f40])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f88,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f87,f40])).

fof(f87,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f83,f45])).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f70,f69])).

fof(f69,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
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
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f70,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f24,f25])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_tarski(X0),X1)
      | r2_hidden(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f79,f47])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f50,f40])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n005.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:44:32 EST 2020
% 0.15/0.35  % CPUTime    : 
% 1.24/0.53  % (9534)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.53  % (9526)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.24/0.53  % (9509)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.54  % (9510)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.54  % (9513)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (9514)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.54  % (9512)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.54  % (9526)Refutation not found, incomplete strategy% (9526)------------------------------
% 1.37/0.54  % (9526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (9531)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.54  % (9511)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (9522)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.55  % (9532)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.55  % (9515)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.55  % (9526)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (9526)Memory used [KB]: 10618
% 1.37/0.55  % (9526)Time elapsed: 0.133 s
% 1.37/0.55  % (9526)------------------------------
% 1.37/0.55  % (9526)------------------------------
% 1.37/0.55  % (9518)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.55  % (9537)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (9528)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (9517)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.55  % (9524)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.55  % (9538)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.55  % (9524)Refutation not found, incomplete strategy% (9524)------------------------------
% 1.37/0.55  % (9524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (9524)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (9524)Memory used [KB]: 6140
% 1.37/0.55  % (9524)Time elapsed: 0.104 s
% 1.37/0.55  % (9524)------------------------------
% 1.37/0.55  % (9524)------------------------------
% 1.37/0.55  % (9529)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.56  % (9516)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.56  % (9533)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.56  % (9520)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.37/0.56  % (9529)Refutation not found, incomplete strategy% (9529)------------------------------
% 1.37/0.56  % (9529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (9529)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (9529)Memory used [KB]: 10746
% 1.37/0.56  % (9529)Time elapsed: 0.145 s
% 1.37/0.56  % (9529)------------------------------
% 1.37/0.56  % (9529)------------------------------
% 1.37/0.56  % (9523)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.56  % (9530)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.56  % (9536)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.56  % (9521)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.56  % (9532)Refutation not found, incomplete strategy% (9532)------------------------------
% 1.37/0.56  % (9532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (9532)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (9532)Memory used [KB]: 1663
% 1.37/0.56  % (9532)Time elapsed: 0.112 s
% 1.37/0.56  % (9532)------------------------------
% 1.37/0.56  % (9532)------------------------------
% 1.37/0.56  % (9525)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.58  % (9527)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.60  % (9519)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.61  % (9519)Refutation not found, incomplete strategy% (9519)------------------------------
% 1.37/0.61  % (9519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.61  % (9535)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.62  % (9519)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.62  
% 1.37/0.62  % (9519)Memory used [KB]: 10618
% 1.37/0.62  % (9519)Time elapsed: 0.176 s
% 1.37/0.62  % (9519)------------------------------
% 1.37/0.62  % (9519)------------------------------
% 2.41/0.72  % (9544)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.41/0.72  % (9542)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.41/0.72  % (9552)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.41/0.73  % (9543)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.41/0.73  % (9516)Refutation found. Thanks to Tanya!
% 2.41/0.73  % SZS status Theorem for theBenchmark
% 2.41/0.73  % SZS output start Proof for theBenchmark
% 2.41/0.73  fof(f1440,plain,(
% 2.41/0.73    $false),
% 2.41/0.73    inference(subsumption_resolution,[],[f1434,f38])).
% 2.41/0.73  fof(f38,plain,(
% 2.41/0.73    ~r2_hidden(sK2,sK1)),
% 2.41/0.73    inference(cnf_transformation,[],[f28])).
% 2.41/0.73  fof(f28,plain,(
% 2.41/0.73    ~r2_hidden(sK2,sK1) & k1_tarski(sK2) = k3_xboole_0(sK1,k1_tarski(sK2))),
% 2.41/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f22,f27])).
% 2.41/0.73  fof(f27,plain,(
% 2.41/0.73    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))) => (~r2_hidden(sK2,sK1) & k1_tarski(sK2) = k3_xboole_0(sK1,k1_tarski(sK2)))),
% 2.41/0.73    introduced(choice_axiom,[])).
% 2.41/0.73  fof(f22,plain,(
% 2.41/0.73    ? [X0,X1] : (~r2_hidden(X1,X0) & k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)))),
% 2.41/0.73    inference(ennf_transformation,[],[f19])).
% 2.41/0.73  fof(f19,negated_conjecture,(
% 2.41/0.73    ~! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 2.41/0.73    inference(negated_conjecture,[],[f18])).
% 2.41/0.73  fof(f18,conjecture,(
% 2.41/0.73    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_zfmisc_1)).
% 2.41/0.73  fof(f1434,plain,(
% 2.41/0.73    r2_hidden(sK2,sK1)),
% 2.41/0.73    inference(superposition,[],[f110,f1423])).
% 2.41/0.73  fof(f1423,plain,(
% 2.41/0.73    sK1 = k2_xboole_0(sK1,k1_tarski(sK2))),
% 2.41/0.73    inference(forward_demodulation,[],[f1400,f363])).
% 2.41/0.73  fof(f363,plain,(
% 2.41/0.73    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.41/0.73    inference(superposition,[],[f342,f334])).
% 2.41/0.73  fof(f334,plain,(
% 2.41/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.41/0.73    inference(forward_demodulation,[],[f310,f191])).
% 2.41/0.73  fof(f191,plain,(
% 2.41/0.73    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.41/0.73    inference(forward_demodulation,[],[f190,f41])).
% 2.41/0.73  fof(f41,plain,(
% 2.41/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.41/0.73    inference(cnf_transformation,[],[f20])).
% 2.41/0.73  fof(f20,plain,(
% 2.41/0.73    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.41/0.73    inference(rectify,[],[f3])).
% 2.41/0.73  fof(f3,axiom,(
% 2.41/0.73    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.41/0.73  fof(f190,plain,(
% 2.41/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.41/0.73    inference(forward_demodulation,[],[f185,f42])).
% 2.41/0.73  fof(f42,plain,(
% 2.41/0.73    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.41/0.73    inference(cnf_transformation,[],[f21])).
% 2.41/0.73  fof(f21,plain,(
% 2.41/0.73    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.41/0.73    inference(rectify,[],[f2])).
% 2.41/0.73  fof(f2,axiom,(
% 2.41/0.73    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.41/0.73  fof(f185,plain,(
% 2.41/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 2.41/0.73    inference(superposition,[],[f46,f39])).
% 2.41/0.73  fof(f39,plain,(
% 2.41/0.73    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.41/0.73    inference(cnf_transformation,[],[f5])).
% 2.41/0.73  fof(f5,axiom,(
% 2.41/0.73    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.41/0.73  fof(f46,plain,(
% 2.41/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.41/0.73    inference(cnf_transformation,[],[f6])).
% 2.41/0.73  fof(f6,axiom,(
% 2.41/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.41/0.73  fof(f310,plain,(
% 2.41/0.73    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.41/0.73    inference(superposition,[],[f49,f39])).
% 2.41/0.73  fof(f49,plain,(
% 2.41/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.41/0.73    inference(cnf_transformation,[],[f4])).
% 2.41/0.73  fof(f4,axiom,(
% 2.41/0.73    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.41/0.73  fof(f342,plain,(
% 2.41/0.73    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.41/0.73    inference(superposition,[],[f334,f43])).
% 2.41/0.73  fof(f43,plain,(
% 2.41/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f1])).
% 2.41/0.73  fof(f1,axiom,(
% 2.41/0.73    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.41/0.73  fof(f1400,plain,(
% 2.41/0.73    k2_xboole_0(sK1,k1_tarski(sK2)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK2)),k1_tarski(sK2))),
% 2.41/0.73    inference(superposition,[],[f347,f37])).
% 2.41/0.73  fof(f37,plain,(
% 2.41/0.73    k1_tarski(sK2) = k3_xboole_0(sK1,k1_tarski(sK2))),
% 2.41/0.73    inference(cnf_transformation,[],[f28])).
% 2.41/0.73  fof(f347,plain,(
% 2.41/0.73    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11))) )),
% 2.41/0.73    inference(superposition,[],[f334,f46])).
% 2.41/0.73  fof(f110,plain,(
% 2.41/0.73    ( ! [X12,X11] : (r2_hidden(X11,k2_xboole_0(X12,k1_tarski(X11)))) )),
% 2.41/0.73    inference(forward_demodulation,[],[f107,f44])).
% 2.41/0.73  fof(f44,plain,(
% 2.41/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.41/0.73    inference(cnf_transformation,[],[f16])).
% 2.41/0.73  fof(f16,axiom,(
% 2.41/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.41/0.73  fof(f107,plain,(
% 2.41/0.73    ( ! [X12,X11] : (r2_hidden(X11,k3_tarski(k2_tarski(X12,k1_tarski(X11))))) )),
% 2.41/0.73    inference(resolution,[],[f80,f90])).
% 2.41/0.73  fof(f90,plain,(
% 2.41/0.73    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 2.41/0.73    inference(resolution,[],[f89,f51])).
% 2.41/0.73  fof(f51,plain,(
% 2.41/0.73    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f30])).
% 2.41/0.73  fof(f30,plain,(
% 2.41/0.73    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.41/0.73    inference(flattening,[],[f29])).
% 2.41/0.73  fof(f29,plain,(
% 2.41/0.73    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.41/0.73    inference(nnf_transformation,[],[f17])).
% 2.41/0.73  fof(f17,axiom,(
% 2.41/0.73    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.41/0.73  fof(f89,plain,(
% 2.41/0.73    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.41/0.73    inference(resolution,[],[f88,f77])).
% 2.41/0.73  fof(f77,plain,(
% 2.41/0.73    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | r1_tarski(X1,X0)) )),
% 2.41/0.73    inference(superposition,[],[f47,f76])).
% 2.41/0.73  fof(f76,plain,(
% 2.41/0.73    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.41/0.73    inference(forward_demodulation,[],[f74,f42])).
% 2.41/0.73  fof(f74,plain,(
% 2.41/0.73    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 2.41/0.73    inference(superposition,[],[f44,f40])).
% 2.41/0.73  fof(f40,plain,(
% 2.41/0.73    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f8])).
% 2.41/0.73  fof(f8,axiom,(
% 2.41/0.73    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.41/0.73  fof(f47,plain,(
% 2.41/0.73    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f23])).
% 2.41/0.73  fof(f23,plain,(
% 2.41/0.73    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.41/0.73    inference(ennf_transformation,[],[f15])).
% 2.41/0.73  fof(f15,axiom,(
% 2.41/0.73    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 2.41/0.73  fof(f88,plain,(
% 2.41/0.73    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 2.41/0.73    inference(superposition,[],[f87,f40])).
% 2.41/0.73  fof(f87,plain,(
% 2.41/0.73    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.41/0.73    inference(superposition,[],[f83,f45])).
% 2.41/0.73  fof(f45,plain,(
% 2.41/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f9])).
% 2.41/0.73  fof(f9,axiom,(
% 2.41/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.41/0.73  fof(f83,plain,(
% 2.41/0.73    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 2.41/0.73    inference(resolution,[],[f70,f69])).
% 2.41/0.73  fof(f69,plain,(
% 2.41/0.73    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 2.41/0.73    inference(equality_resolution,[],[f55])).
% 2.41/0.73  fof(f55,plain,(
% 2.41/0.73    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f35])).
% 2.41/0.73  fof(f35,plain,(
% 2.41/0.73    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.41/0.73    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 2.41/0.73  fof(f34,plain,(
% 2.41/0.73    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 2.41/0.73    introduced(choice_axiom,[])).
% 2.41/0.73  fof(f33,plain,(
% 2.41/0.73    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.41/0.73    inference(rectify,[],[f32])).
% 2.41/0.73  fof(f32,plain,(
% 2.41/0.73    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 2.41/0.73    inference(flattening,[],[f31])).
% 2.41/0.73  fof(f31,plain,(
% 2.41/0.73    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 2.41/0.73    inference(nnf_transformation,[],[f25])).
% 2.41/0.73  fof(f25,plain,(
% 2.41/0.73    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.41/0.73    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.41/0.73  fof(f70,plain,(
% 2.41/0.73    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 2.41/0.73    inference(equality_resolution,[],[f62])).
% 2.41/0.73  fof(f62,plain,(
% 2.41/0.73    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.41/0.73    inference(cnf_transformation,[],[f36])).
% 2.41/0.73  fof(f36,plain,(
% 2.41/0.73    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 2.41/0.73    inference(nnf_transformation,[],[f26])).
% 2.41/0.73  fof(f26,plain,(
% 2.41/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 2.41/0.73    inference(definition_folding,[],[f24,f25])).
% 2.41/0.73  fof(f24,plain,(
% 2.41/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.41/0.73    inference(ennf_transformation,[],[f7])).
% 2.41/0.73  fof(f7,axiom,(
% 2.41/0.73    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.41/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.41/0.73  fof(f80,plain,(
% 2.41/0.73    ( ! [X0,X1] : (~r2_hidden(k1_tarski(X0),X1) | r2_hidden(X0,k3_tarski(X1))) )),
% 2.41/0.73    inference(resolution,[],[f79,f47])).
% 2.41/0.73  fof(f79,plain,(
% 2.41/0.73    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.41/0.73    inference(superposition,[],[f50,f40])).
% 2.41/0.73  fof(f50,plain,(
% 2.41/0.73    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.41/0.73    inference(cnf_transformation,[],[f30])).
% 2.41/0.73  % SZS output end Proof for theBenchmark
% 2.41/0.73  % (9516)------------------------------
% 2.41/0.73  % (9516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.41/0.73  % (9516)Termination reason: Refutation
% 2.41/0.73  
% 2.41/0.73  % (9516)Memory used [KB]: 8059
% 2.41/0.73  % (9516)Time elapsed: 0.273 s
% 2.41/0.73  % (9516)------------------------------
% 2.41/0.73  % (9516)------------------------------
% 2.41/0.76  % (9508)Success in time 0.39 s
%------------------------------------------------------------------------------
