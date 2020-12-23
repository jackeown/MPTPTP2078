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
% DateTime   : Thu Dec  3 12:40:30 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 114 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  190 ( 252 expanded)
%              Number of equality atoms :  111 ( 165 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1497,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1491,f41])).

fof(f41,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_hidden(sK1,sK3)
    & k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) )
   => ( ~ r2_hidden(sK1,sK3)
      & k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f1491,plain,(
    r2_hidden(sK1,sK3) ),
    inference(superposition,[],[f152,f1479])).

fof(f1479,plain,(
    sK3 = k2_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(forward_demodulation,[],[f1456,f453])).

fof(f453,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f431,f431])).

fof(f431,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f427,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f427,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f403,f315])).

fof(f315,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f314,f44])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f314,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f309,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f309,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f49,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f403,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f52,f42])).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1456,plain,(
    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f436,f40])).

fof(f40,plain,(
    k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f436,plain,(
    ! [X10,X11] : k2_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11)) ),
    inference(superposition,[],[f427,f49])).

fof(f152,plain,(
    ! [X21,X22,X20] : r2_hidden(X20,k2_xboole_0(k2_tarski(X20,X21),X22)) ),
    inference(forward_demodulation,[],[f143,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f143,plain,(
    ! [X21,X22,X20] : r2_hidden(X20,k3_tarski(k2_tarski(k2_tarski(X20,X21),X22))) ),
    inference(resolution,[],[f84,f93])).

fof(f93,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f89,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f89,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP0(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK4(X0,X1,X2,X3) != X0
              & sK4(X0,X1,X2,X3) != X1
              & sK4(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sK4(X0,X1,X2,X3) = X0
            | sK4(X0,X1,X2,X3) = X1
            | sK4(X0,X1,X2,X3) = X2
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
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
     => ( ( ( sK4(X0,X1,X2,X3) != X0
            & sK4(X0,X1,X2,X3) != X1
            & sK4(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sK4(X0,X1,X2,X3) = X0
          | sK4(X0,X1,X2,X3) = X1
          | sK4(X0,X1,X2,X3) = X2
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f76,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f27,f28])).

fof(f27,plain,(
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

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k2_tarski(X0,X2),X1)
      | r2_hidden(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.50  % (11537)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.50  % (11535)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (11531)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (11543)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (11537)Refutation not found, incomplete strategy% (11537)------------------------------
% 0.19/0.51  % (11537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (11537)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (11537)Memory used [KB]: 10618
% 0.19/0.51  % (11537)Time elapsed: 0.091 s
% 0.19/0.51  % (11537)------------------------------
% 0.19/0.51  % (11537)------------------------------
% 0.19/0.51  % (11532)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (11534)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.51  % (11553)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.51  % (11545)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.51  % (11533)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (11527)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.52  % (11544)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.52  % (11541)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.52  % (11529)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.52  % (11530)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (11538)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.52  % (11547)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.52  % (11551)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.52  % (11547)Refutation not found, incomplete strategy% (11547)------------------------------
% 0.19/0.52  % (11547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (11547)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (11547)Memory used [KB]: 10746
% 0.19/0.52  % (11547)Time elapsed: 0.121 s
% 0.19/0.52  % (11547)------------------------------
% 0.19/0.52  % (11547)------------------------------
% 0.19/0.52  % (11552)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.52  % (11549)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.53  % (11548)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.53  % (11555)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.53  % (11536)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.53  % (11528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (11554)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.53  % (11540)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.54  % (11539)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (11556)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.54  % (11544)Refutation not found, incomplete strategy% (11544)------------------------------
% 1.37/0.54  % (11544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (11544)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (11544)Memory used [KB]: 10618
% 1.37/0.54  % (11544)Time elapsed: 0.135 s
% 1.37/0.54  % (11544)------------------------------
% 1.37/0.54  % (11544)------------------------------
% 1.37/0.55  % (11546)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.37/0.55  % (11542)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.56  % (11550)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.55/0.56  % (11550)Refutation not found, incomplete strategy% (11550)------------------------------
% 1.55/0.56  % (11550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (11550)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (11550)Memory used [KB]: 1663
% 1.55/0.56  % (11550)Time elapsed: 0.159 s
% 1.55/0.56  % (11550)------------------------------
% 1.55/0.56  % (11550)------------------------------
% 1.55/0.56  % (11542)Refutation not found, incomplete strategy% (11542)------------------------------
% 1.55/0.56  % (11542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (11542)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (11542)Memory used [KB]: 6140
% 1.55/0.56  % (11542)Time elapsed: 0.160 s
% 1.55/0.56  % (11542)------------------------------
% 1.55/0.56  % (11542)------------------------------
% 2.05/0.67  % (11557)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.38/0.69  % (11534)Refutation found. Thanks to Tanya!
% 2.38/0.69  % SZS status Theorem for theBenchmark
% 2.38/0.69  % SZS output start Proof for theBenchmark
% 2.38/0.69  fof(f1497,plain,(
% 2.38/0.69    $false),
% 2.38/0.69    inference(subsumption_resolution,[],[f1491,f41])).
% 2.38/0.69  fof(f41,plain,(
% 2.38/0.69    ~r2_hidden(sK1,sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f31])).
% 2.38/0.69  fof(f31,plain,(
% 2.38/0.69    ~r2_hidden(sK1,sK3) & k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f30])).
% 2.38/0.69  fof(f30,plain,(
% 2.38/0.69    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)) => (~r2_hidden(sK1,sK3) & k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),sK3))),
% 2.38/0.69    introduced(choice_axiom,[])).
% 2.38/0.69  fof(f25,plain,(
% 2.38/0.69    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 2.38/0.69    inference(ennf_transformation,[],[f22])).
% 2.38/0.69  fof(f22,negated_conjecture,(
% 2.38/0.69    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 2.38/0.69    inference(negated_conjecture,[],[f21])).
% 2.38/0.69  fof(f21,conjecture,(
% 2.38/0.69    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 2.38/0.69  fof(f1491,plain,(
% 2.38/0.69    r2_hidden(sK1,sK3)),
% 2.38/0.69    inference(superposition,[],[f152,f1479])).
% 2.38/0.69  fof(f1479,plain,(
% 2.38/0.69    sK3 = k2_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.38/0.69    inference(forward_demodulation,[],[f1456,f453])).
% 2.38/0.69  fof(f453,plain,(
% 2.38/0.69    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 2.38/0.69    inference(superposition,[],[f431,f431])).
% 2.38/0.69  fof(f431,plain,(
% 2.38/0.69    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.38/0.69    inference(superposition,[],[f427,f46])).
% 2.38/0.69  fof(f46,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f1])).
% 2.38/0.69  fof(f1,axiom,(
% 2.38/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.38/0.69  fof(f427,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.38/0.69    inference(forward_demodulation,[],[f403,f315])).
% 2.38/0.69  fof(f315,plain,(
% 2.38/0.69    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.38/0.69    inference(forward_demodulation,[],[f314,f44])).
% 2.38/0.69  fof(f44,plain,(
% 2.38/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.38/0.69    inference(cnf_transformation,[],[f23])).
% 2.38/0.69  fof(f23,plain,(
% 2.38/0.69    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.38/0.69    inference(rectify,[],[f3])).
% 2.38/0.69  fof(f3,axiom,(
% 2.38/0.69    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.38/0.69  fof(f314,plain,(
% 2.38/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.38/0.69    inference(forward_demodulation,[],[f309,f45])).
% 2.38/0.69  fof(f45,plain,(
% 2.38/0.69    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.38/0.69    inference(cnf_transformation,[],[f24])).
% 2.38/0.69  fof(f24,plain,(
% 2.38/0.69    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.38/0.69    inference(rectify,[],[f2])).
% 2.38/0.69  fof(f2,axiom,(
% 2.38/0.69    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.38/0.69  fof(f309,plain,(
% 2.38/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 2.38/0.69    inference(superposition,[],[f49,f42])).
% 2.38/0.69  fof(f42,plain,(
% 2.38/0.69    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.38/0.69    inference(cnf_transformation,[],[f5])).
% 2.38/0.69  fof(f5,axiom,(
% 2.38/0.69    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.38/0.69  fof(f49,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.38/0.69    inference(cnf_transformation,[],[f6])).
% 2.38/0.69  fof(f6,axiom,(
% 2.38/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.38/0.69  fof(f403,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.38/0.69    inference(superposition,[],[f52,f42])).
% 2.38/0.69  fof(f52,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.38/0.69    inference(cnf_transformation,[],[f4])).
% 2.38/0.69  fof(f4,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.38/0.69  fof(f1456,plain,(
% 2.38/0.69    k2_xboole_0(k2_tarski(sK1,sK2),sK3) = k5_xboole_0(k5_xboole_0(k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))),
% 2.38/0.69    inference(superposition,[],[f436,f40])).
% 2.38/0.69  fof(f40,plain,(
% 2.38/0.69    k2_tarski(sK1,sK2) = k3_xboole_0(k2_tarski(sK1,sK2),sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f31])).
% 2.38/0.69  fof(f436,plain,(
% 2.38/0.69    ( ! [X10,X11] : (k2_xboole_0(X10,X11) = k5_xboole_0(k5_xboole_0(X10,X11),k3_xboole_0(X10,X11))) )),
% 2.38/0.69    inference(superposition,[],[f427,f49])).
% 2.38/0.69  fof(f152,plain,(
% 2.38/0.69    ( ! [X21,X22,X20] : (r2_hidden(X20,k2_xboole_0(k2_tarski(X20,X21),X22))) )),
% 2.38/0.69    inference(forward_demodulation,[],[f143,f47])).
% 2.38/0.69  fof(f47,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.38/0.69    inference(cnf_transformation,[],[f19])).
% 2.38/0.69  fof(f19,axiom,(
% 2.38/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.38/0.69  fof(f143,plain,(
% 2.38/0.69    ( ! [X21,X22,X20] : (r2_hidden(X20,k3_tarski(k2_tarski(k2_tarski(X20,X21),X22)))) )),
% 2.38/0.69    inference(resolution,[],[f84,f93])).
% 2.38/0.69  fof(f93,plain,(
% 2.38/0.69    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.38/0.69    inference(superposition,[],[f89,f48])).
% 2.38/0.69  fof(f48,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f12])).
% 2.38/0.69  fof(f12,axiom,(
% 2.38/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.38/0.69  fof(f89,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 2.38/0.69    inference(resolution,[],[f76,f75])).
% 2.38/0.69  fof(f75,plain,(
% 2.38/0.69    ( ! [X0,X5,X3,X1] : (~sP0(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 2.38/0.69    inference(equality_resolution,[],[f59])).
% 2.38/0.69  fof(f59,plain,(
% 2.38/0.69    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f38])).
% 2.38/0.69  fof(f38,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.38/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 2.38/0.69  fof(f37,plain,(
% 2.38/0.69    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK4(X0,X1,X2,X3) != X0 & sK4(X0,X1,X2,X3) != X1 & sK4(X0,X1,X2,X3) != X2) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sK4(X0,X1,X2,X3) = X0 | sK4(X0,X1,X2,X3) = X1 | sK4(X0,X1,X2,X3) = X2 | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 2.38/0.69    introduced(choice_axiom,[])).
% 2.38/0.69  fof(f36,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.38/0.69    inference(rectify,[],[f35])).
% 2.38/0.69  fof(f35,plain,(
% 2.38/0.69    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 2.38/0.69    inference(flattening,[],[f34])).
% 2.38/0.69  fof(f34,plain,(
% 2.38/0.69    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 2.38/0.69    inference(nnf_transformation,[],[f28])).
% 2.38/0.69  fof(f28,plain,(
% 2.38/0.69    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.38/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.38/0.69  fof(f76,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 2.38/0.69    inference(equality_resolution,[],[f66])).
% 2.38/0.69  fof(f66,plain,(
% 2.38/0.69    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.38/0.69    inference(cnf_transformation,[],[f39])).
% 2.38/0.69  fof(f39,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 2.38/0.69    inference(nnf_transformation,[],[f29])).
% 2.38/0.69  fof(f29,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 2.38/0.69    inference(definition_folding,[],[f27,f28])).
% 2.38/0.69  fof(f27,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.38/0.69    inference(ennf_transformation,[],[f7])).
% 2.38/0.69  fof(f7,axiom,(
% 2.38/0.69    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 2.38/0.69  fof(f84,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~r2_hidden(k2_tarski(X0,X2),X1) | r2_hidden(X0,k3_tarski(X1))) )),
% 2.38/0.69    inference(resolution,[],[f53,f50])).
% 2.38/0.69  fof(f50,plain,(
% 2.38/0.69    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f26])).
% 2.38/0.69  fof(f26,plain,(
% 2.38/0.69    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f18])).
% 2.38/0.69  fof(f18,axiom,(
% 2.38/0.69    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 2.38/0.69  fof(f53,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f33])).
% 2.38/0.69  fof(f33,plain,(
% 2.38/0.69    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.38/0.69    inference(flattening,[],[f32])).
% 2.38/0.69  fof(f32,plain,(
% 2.38/0.69    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.38/0.69    inference(nnf_transformation,[],[f20])).
% 2.38/0.69  fof(f20,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.38/0.69  % SZS output end Proof for theBenchmark
% 2.38/0.69  % (11534)------------------------------
% 2.38/0.69  % (11534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.69  % (11534)Termination reason: Refutation
% 2.38/0.69  
% 2.38/0.69  % (11534)Memory used [KB]: 8059
% 2.38/0.69  % (11534)Time elapsed: 0.288 s
% 2.38/0.69  % (11534)------------------------------
% 2.38/0.69  % (11534)------------------------------
% 2.38/0.69  % (11526)Success in time 0.335 s
%------------------------------------------------------------------------------
