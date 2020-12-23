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
% DateTime   : Thu Dec  3 12:41:00 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 134 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   28
%              Number of atoms          :  228 ( 437 expanded)
%              Number of equality atoms :  123 ( 187 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f112])).

fof(f112,plain,(
    r1_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f47,f109])).

fof(f109,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f78,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f78,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f73,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f38,f71])).

fof(f71,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f69,f39])).

fof(f69,plain,
    ( k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)
    | k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f68,f46])).

fof(f68,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f34,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f34,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,(
    ~ r1_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f163,f37])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f163,plain,(
    ! [X0] : ~ r1_xboole_0(sK1,k2_tarski(X0,sK0)) ),
    inference(superposition,[],[f145,f40])).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f145,plain,(
    ! [X2,X1] : ~ r1_xboole_0(sK1,k1_enumset1(X1,X2,sK0)) ),
    inference(resolution,[],[f141,f62])).

fof(f62,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f141,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | ~ r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f140,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f26])).

% (13978)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f140,plain,(
    r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k1_tarski(sK0) != k1_tarski(sK0)
    | r2_hidden(sK0,sK1) ),
    inference(backward_demodulation,[],[f35,f138])).

fof(f138,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f134,f36])).

fof(f36,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f134,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f41,f129])).

fof(f129,plain,(
    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f128,f46])).

fof(f128,plain,(
    r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,
    ( r1_xboole_0(k1_tarski(sK0),sK1)
    | r1_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f119,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f119,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2(k1_tarski(sK0),X2),sK1)
      | r1_xboole_0(k1_tarski(sK0),X2) ) ),
    inference(resolution,[],[f115,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tarski(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f112,f44])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:18:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 1.33/0.53  % (13969)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.55  % (13992)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.56  % (13984)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.49/0.56  % (13985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.49/0.56  % (13971)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.49/0.57  % (13968)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.49/0.57  % (13975)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.57  % (13992)Refutation found. Thanks to Tanya!
% 1.49/0.57  % SZS status Theorem for theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f172,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(subsumption_resolution,[],[f171,f112])).
% 1.49/0.57  fof(f112,plain,(
% 1.49/0.57    r1_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(trivial_inequality_removal,[],[f110])).
% 1.49/0.57  fof(f110,plain,(
% 1.49/0.57    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(superposition,[],[f47,f109])).
% 1.49/0.57  fof(f109,plain,(
% 1.49/0.57    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(duplicate_literal_removal,[],[f99])).
% 1.49/0.57  fof(f99,plain,(
% 1.49/0.57    k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0)) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(superposition,[],[f78,f39])).
% 1.49/0.57  fof(f39,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.49/0.57  fof(f78,plain,(
% 1.49/0.57    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(resolution,[],[f73,f46])).
% 1.49/0.57  fof(f46,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f28,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.49/0.57    inference(nnf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.49/0.57  fof(f73,plain,(
% 1.49/0.57    r1_xboole_0(k1_tarski(sK0),sK1) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(superposition,[],[f38,f71])).
% 1.49/0.57  fof(f71,plain,(
% 1.49/0.57    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | k1_xboole_0 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(forward_demodulation,[],[f69,f39])).
% 1.49/0.57  fof(f69,plain,(
% 1.49/0.57    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) | k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(resolution,[],[f68,f46])).
% 1.49/0.57  fof(f68,plain,(
% 1.49/0.57    r1_xboole_0(k1_tarski(sK0),sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(resolution,[],[f34,f45])).
% 1.49/0.57  fof(f45,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f21,plain,(
% 1.49/0.57    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f15])).
% 1.49/0.57  fof(f15,axiom,(
% 1.49/0.57    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.49/0.57  fof(f34,plain,(
% 1.49/0.57    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f25])).
% 1.49/0.57  fof(f25,plain,(
% 1.49/0.57    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.49/0.57    inference(nnf_transformation,[],[f19])).
% 1.49/0.57  fof(f19,plain,(
% 1.49/0.57    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.49/0.57    inference(ennf_transformation,[],[f17])).
% 1.49/0.57  fof(f17,negated_conjecture,(
% 1.49/0.57    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.49/0.57    inference(negated_conjecture,[],[f16])).
% 1.49/0.57  fof(f16,conjecture,(
% 1.49/0.57    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.49/0.57  fof(f38,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.49/0.57  fof(f47,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f171,plain,(
% 1.49/0.57    ~r1_xboole_0(sK1,k1_tarski(sK0))),
% 1.49/0.57    inference(superposition,[],[f163,f37])).
% 1.49/0.57  fof(f37,plain,(
% 1.49/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.49/0.57  fof(f163,plain,(
% 1.49/0.57    ( ! [X0] : (~r1_xboole_0(sK1,k2_tarski(X0,sK0))) )),
% 1.49/0.57    inference(superposition,[],[f145,f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f9])).
% 1.49/0.57  fof(f9,axiom,(
% 1.49/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.49/0.57  fof(f145,plain,(
% 1.49/0.57    ( ! [X2,X1] : (~r1_xboole_0(sK1,k1_enumset1(X1,X2,sK0))) )),
% 1.49/0.57    inference(resolution,[],[f141,f62])).
% 1.49/0.57  fof(f62,plain,(
% 1.49/0.57    ( ! [X0,X5,X1] : (r2_hidden(X5,k1_enumset1(X0,X1,X5))) )),
% 1.49/0.57    inference(equality_resolution,[],[f61])).
% 1.49/0.57  fof(f61,plain,(
% 1.49/0.57    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X0,X1,X5) != X3) )),
% 1.49/0.57    inference(equality_resolution,[],[f53])).
% 1.49/0.57  fof(f53,plain,(
% 1.49/0.57    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.49/0.57    inference(cnf_transformation,[],[f33])).
% 1.49/0.57  fof(f33,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.49/0.57  fof(f32,plain,(
% 1.49/0.57    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f31,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.49/0.57    inference(rectify,[],[f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.49/0.57    inference(flattening,[],[f29])).
% 1.49/0.57  fof(f29,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.49/0.57    inference(nnf_transformation,[],[f22])).
% 1.49/0.57  fof(f22,plain,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.49/0.57    inference(ennf_transformation,[],[f7])).
% 1.49/0.57  fof(f7,axiom,(
% 1.49/0.57    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.49/0.57  fof(f141,plain,(
% 1.49/0.57    ( ! [X0] : (~r2_hidden(sK0,X0) | ~r1_xboole_0(sK1,X0)) )),
% 1.49/0.57    inference(resolution,[],[f140,f44])).
% 1.49/0.57  fof(f44,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f27])).
% 1.49/0.57  fof(f27,plain,(
% 1.49/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f26])).
% 1.49/0.57  % (13978)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f20,plain,(
% 1.49/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.49/0.57    inference(ennf_transformation,[],[f18])).
% 1.49/0.57  fof(f18,plain,(
% 1.49/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.49/0.57    inference(rectify,[],[f3])).
% 1.49/0.57  fof(f3,axiom,(
% 1.49/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.49/0.57  fof(f140,plain,(
% 1.49/0.57    r2_hidden(sK0,sK1)),
% 1.49/0.57    inference(trivial_inequality_removal,[],[f139])).
% 1.49/0.57  fof(f139,plain,(
% 1.49/0.57    k1_tarski(sK0) != k1_tarski(sK0) | r2_hidden(sK0,sK1)),
% 1.49/0.57    inference(backward_demodulation,[],[f35,f138])).
% 1.49/0.57  fof(f138,plain,(
% 1.49/0.57    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(forward_demodulation,[],[f134,f36])).
% 1.49/0.57  fof(f36,plain,(
% 1.49/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.57    inference(cnf_transformation,[],[f5])).
% 1.49/0.57  fof(f5,axiom,(
% 1.49/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.49/0.57  fof(f134,plain,(
% 1.49/0.57    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 1.49/0.57    inference(superposition,[],[f41,f129])).
% 1.49/0.57  fof(f129,plain,(
% 1.49/0.57    k1_xboole_0 = k3_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(resolution,[],[f128,f46])).
% 1.49/0.57  fof(f128,plain,(
% 1.49/0.57    r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(duplicate_literal_removal,[],[f126])).
% 1.49/0.57  fof(f126,plain,(
% 1.49/0.57    r1_xboole_0(k1_tarski(sK0),sK1) | r1_xboole_0(k1_tarski(sK0),sK1)),
% 1.49/0.57    inference(resolution,[],[f119,f43])).
% 1.49/0.57  fof(f43,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f27])).
% 1.49/0.57  fof(f119,plain,(
% 1.49/0.57    ( ! [X2] : (~r2_hidden(sK2(k1_tarski(sK0),X2),sK1) | r1_xboole_0(k1_tarski(sK0),X2)) )),
% 1.49/0.57    inference(resolution,[],[f115,f42])).
% 1.49/0.57  fof(f42,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f27])).
% 1.49/0.57  fof(f115,plain,(
% 1.49/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tarski(sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.49/0.57    inference(resolution,[],[f112,f44])).
% 1.49/0.57  fof(f41,plain,(
% 1.49/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f4])).
% 1.49/0.57  fof(f4,axiom,(
% 1.49/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f25])).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (13992)------------------------------
% 1.49/0.57  % (13992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (13992)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (13992)Memory used [KB]: 1791
% 1.49/0.57  % (13992)Time elapsed: 0.089 s
% 1.49/0.57  % (13992)------------------------------
% 1.49/0.57  % (13992)------------------------------
% 1.49/0.57  % (13993)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.49/0.58  % (13967)Success in time 0.223 s
%------------------------------------------------------------------------------
