%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:01 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 202 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  202 ( 777 expanded)
%              Number of equality atoms :   32 ( 144 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f346,plain,(
    $false ),
    inference(subsumption_resolution,[],[f345,f72])).

fof(f72,plain,(
    r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f39,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f39,plain,
    ( r2_hidden(sK1,sK2)
    | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( r2_hidden(sK1,sK2)
      | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2) )
    & ( ~ r2_hidden(sK1,sK2)
      | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK1,sK2)
        | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2) )
      & ( ~ r2_hidden(sK1,sK2)
        | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

% (13650)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f345,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f339,f140])).

fof(f140,plain,(
    r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(resolution,[],[f128,f65])).

fof(f65,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f2,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ sP0(X2,X3,k3_xboole_0(sK2,k1_tarski(sK1)))
      | r2_hidden(sK1,X2) ) ),
    inference(resolution,[],[f118,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f118,plain,(
    r2_hidden(sK1,k3_xboole_0(sK2,k1_tarski(sK1))) ),
    inference(resolution,[],[f109,f66])).

fof(f66,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f109,plain,(
    ! [X0] :
      ( r2_hidden(sK1,k4_xboole_0(sK2,X0))
      | r2_hidden(sK1,k3_xboole_0(sK2,X0)) ) ),
    inference(superposition,[],[f100,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f100,plain,(
    ! [X2] :
      ( r2_hidden(sK1,k5_xboole_0(sK2,X2))
      | r2_hidden(sK1,X2) ) ),
    inference(resolution,[],[f59,f72])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f339,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,sK2) ),
    inference(superposition,[],[f334,f73])).

fof(f73,plain,(
    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f38,f72])).

fof(f38,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

% (13648)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f334,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k4_xboole_0(k1_tarski(sK1),X0))
      | ~ r2_hidden(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f330,f140])).

fof(f330,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k4_xboole_0(k1_tarski(sK1),X0))
      | ~ r2_hidden(sK1,k1_tarski(sK1))
      | ~ r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f161,f278])).

fof(f278,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f51,f65])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f161,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,k3_xboole_0(k1_tarski(sK1),X0))
      | ~ r2_hidden(sK1,k4_xboole_0(k1_tarski(sK1),X0)) ) ),
    inference(superposition,[],[f144,f45])).

fof(f144,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),X1))
      | ~ r2_hidden(sK1,X1) ) ),
    inference(resolution,[],[f140,f58])).

% (13644)Refutation not found, incomplete strategy% (13644)------------------------------
% (13644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

% (13644)Termination reason: Refutation not found, incomplete strategy

% (13644)Memory used [KB]: 1663
% (13644)Time elapsed: 0.188 s
% (13644)------------------------------
% (13644)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (13629)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (13628)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (13646)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (13637)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (13638)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (13645)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (13645)Refutation not found, incomplete strategy% (13645)------------------------------
% 0.21/0.54  % (13645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (13645)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (13645)Memory used [KB]: 10746
% 0.21/0.54  % (13645)Time elapsed: 0.127 s
% 0.21/0.54  % (13645)------------------------------
% 0.21/0.54  % (13645)------------------------------
% 0.21/0.55  % (13630)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (13626)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (13627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (13625)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (13625)Refutation not found, incomplete strategy% (13625)------------------------------
% 0.21/0.56  % (13625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13625)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (13625)Memory used [KB]: 10618
% 0.21/0.56  % (13625)Time elapsed: 0.144 s
% 0.21/0.56  % (13625)------------------------------
% 0.21/0.56  % (13625)------------------------------
% 0.21/0.56  % (13624)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.58  % (13644)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.62/0.59  % (13636)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.59  % (13649)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.62/0.59  % (13652)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.60  % (13623)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.60  % (13641)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.62/0.60  % (13630)Refutation found. Thanks to Tanya!
% 1.62/0.60  % SZS status Theorem for theBenchmark
% 1.62/0.60  % (13651)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.62/0.60  % SZS output start Proof for theBenchmark
% 1.62/0.60  fof(f346,plain,(
% 1.62/0.60    $false),
% 1.62/0.60    inference(subsumption_resolution,[],[f345,f72])).
% 1.62/0.60  fof(f72,plain,(
% 1.62/0.60    r2_hidden(sK1,sK2)),
% 1.62/0.60    inference(subsumption_resolution,[],[f39,f71])).
% 1.62/0.60  fof(f71,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.62/0.60    inference(resolution,[],[f47,f46])).
% 1.62/0.60  fof(f46,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f19])).
% 1.62/0.60  fof(f19,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f12])).
% 1.62/0.60  fof(f12,axiom,(
% 1.62/0.60    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.62/0.60  fof(f47,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f20])).
% 1.62/0.60  fof(f20,plain,(
% 1.62/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f16])).
% 1.62/0.60  fof(f16,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.62/0.60    inference(unused_predicate_definition_removal,[],[f7])).
% 1.62/0.60  fof(f7,axiom,(
% 1.62/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.62/0.60  fof(f39,plain,(
% 1.62/0.60    r2_hidden(sK1,sK2) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.62/0.60    inference(cnf_transformation,[],[f26])).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    (r2_hidden(sK1,sK2) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2)) & (~r2_hidden(sK1,sK2) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).
% 1.62/0.60  fof(f25,plain,(
% 1.62/0.60    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK1,sK2) | k1_tarski(sK1) != k4_xboole_0(k1_tarski(sK1),sK2)) & (~r2_hidden(sK1,sK2) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2)))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f24,plain,(
% 1.62/0.60    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.62/0.60    inference(nnf_transformation,[],[f17])).
% 1.62/0.60  fof(f17,plain,(
% 1.62/0.60    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f15])).
% 1.62/0.60  fof(f15,negated_conjecture,(
% 1.62/0.60    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.62/0.60    inference(negated_conjecture,[],[f14])).
% 1.62/0.60  fof(f14,conjecture,(
% 1.62/0.60    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.62/0.60  % (13650)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.60  fof(f345,plain,(
% 1.62/0.60    ~r2_hidden(sK1,sK2)),
% 1.62/0.60    inference(subsumption_resolution,[],[f339,f140])).
% 1.62/0.60  fof(f140,plain,(
% 1.62/0.60    r2_hidden(sK1,k1_tarski(sK1))),
% 1.62/0.60    inference(resolution,[],[f128,f65])).
% 1.62/0.60  fof(f65,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.60    inference(equality_resolution,[],[f55])).
% 1.62/0.60  fof(f55,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.62/0.60    inference(cnf_transformation,[],[f34])).
% 1.62/0.60  fof(f34,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.62/0.60    inference(nnf_transformation,[],[f23])).
% 1.62/0.60  fof(f23,plain,(
% 1.62/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.62/0.60    inference(definition_folding,[],[f2,f22])).
% 1.62/0.60  fof(f22,plain,(
% 1.62/0.60    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.60    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.62/0.60  fof(f2,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.62/0.60  fof(f128,plain,(
% 1.62/0.60    ( ! [X2,X3] : (~sP0(X2,X3,k3_xboole_0(sK2,k1_tarski(sK1))) | r2_hidden(sK1,X2)) )),
% 1.62/0.60    inference(resolution,[],[f118,f50])).
% 1.62/0.60  fof(f50,plain,(
% 1.62/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f33])).
% 1.62/0.60  fof(f33,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.62/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 1.62/0.60  fof(f32,plain,(
% 1.62/0.60    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.62/0.60    introduced(choice_axiom,[])).
% 1.62/0.60  fof(f31,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.62/0.60    inference(rectify,[],[f30])).
% 1.62/0.60  fof(f30,plain,(
% 1.62/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.62/0.60    inference(flattening,[],[f29])).
% 1.62/0.60  fof(f29,plain,(
% 1.62/0.60    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.62/0.60    inference(nnf_transformation,[],[f22])).
% 1.62/0.60  fof(f118,plain,(
% 1.62/0.60    r2_hidden(sK1,k3_xboole_0(sK2,k1_tarski(sK1)))),
% 1.62/0.60    inference(resolution,[],[f109,f66])).
% 1.62/0.60  fof(f66,plain,(
% 1.62/0.60    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.62/0.60    inference(equality_resolution,[],[f62])).
% 1.62/0.60  fof(f62,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f37])).
% 1.62/0.60  fof(f37,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.62/0.60    inference(flattening,[],[f36])).
% 1.62/0.60  fof(f36,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.62/0.60    inference(nnf_transformation,[],[f13])).
% 1.62/0.60  fof(f13,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.62/0.60  fof(f109,plain,(
% 1.62/0.60    ( ! [X0] : (r2_hidden(sK1,k4_xboole_0(sK2,X0)) | r2_hidden(sK1,k3_xboole_0(sK2,X0))) )),
% 1.62/0.60    inference(superposition,[],[f100,f45])).
% 1.62/0.60  fof(f45,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f5])).
% 1.62/0.60  fof(f5,axiom,(
% 1.62/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.60  fof(f100,plain,(
% 1.62/0.60    ( ! [X2] : (r2_hidden(sK1,k5_xboole_0(sK2,X2)) | r2_hidden(sK1,X2)) )),
% 1.62/0.60    inference(resolution,[],[f59,f72])).
% 1.62/0.60  fof(f59,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f35])).
% 1.62/0.60  fof(f35,plain,(
% 1.62/0.60    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 1.62/0.60    inference(nnf_transformation,[],[f21])).
% 1.62/0.60  fof(f21,plain,(
% 1.62/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.62/0.60    inference(ennf_transformation,[],[f3])).
% 1.62/0.60  fof(f3,axiom,(
% 1.62/0.60    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.62/0.60  fof(f339,plain,(
% 1.62/0.60    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,sK2)),
% 1.62/0.60    inference(superposition,[],[f334,f73])).
% 1.62/0.60  fof(f73,plain,(
% 1.62/0.60    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.62/0.60    inference(subsumption_resolution,[],[f38,f72])).
% 1.62/0.60  fof(f38,plain,(
% 1.62/0.60    ~r2_hidden(sK1,sK2) | k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.62/0.60    inference(cnf_transformation,[],[f26])).
% 1.62/0.60  % (13648)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.62/0.60  fof(f334,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(k1_tarski(sK1),X0)) | ~r2_hidden(sK1,X0)) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f330,f140])).
% 1.62/0.60  fof(f330,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(sK1,k4_xboole_0(k1_tarski(sK1),X0)) | ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,X0)) )),
% 1.62/0.60    inference(resolution,[],[f161,f278])).
% 1.62/0.60  fof(f278,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_xboole_0(X2,X1)) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.62/0.60    inference(resolution,[],[f51,f65])).
% 1.62/0.60  fof(f51,plain,(
% 1.62/0.60    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1) | r2_hidden(X4,X2)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f33])).
% 1.62/0.60  fof(f161,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(sK1,k3_xboole_0(k1_tarski(sK1),X0)) | ~r2_hidden(sK1,k4_xboole_0(k1_tarski(sK1),X0))) )),
% 1.62/0.60    inference(superposition,[],[f144,f45])).
% 1.62/0.60  fof(f144,plain,(
% 1.62/0.60    ( ! [X1] : (~r2_hidden(sK1,k5_xboole_0(k1_tarski(sK1),X1)) | ~r2_hidden(sK1,X1)) )),
% 1.62/0.60    inference(resolution,[],[f140,f58])).
% 1.62/0.60  % (13644)Refutation not found, incomplete strategy% (13644)------------------------------
% 1.62/0.60  % (13644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  fof(f58,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f35])).
% 1.62/0.60  % (13644)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.60  
% 1.62/0.60  % (13644)Memory used [KB]: 1663
% 1.62/0.60  % (13644)Time elapsed: 0.188 s
% 1.62/0.60  % (13644)------------------------------
% 1.62/0.60  % (13644)------------------------------
% 1.62/0.60  % SZS output end Proof for theBenchmark
% 1.62/0.60  % (13630)------------------------------
% 1.62/0.60  % (13630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (13630)Termination reason: Refutation
% 1.62/0.60  
% 1.62/0.60  % (13630)Memory used [KB]: 6524
% 1.62/0.60  % (13630)Time elapsed: 0.134 s
% 1.62/0.60  % (13630)------------------------------
% 1.62/0.60  % (13630)------------------------------
% 1.62/0.60  % (13622)Success in time 0.243 s
%------------------------------------------------------------------------------
