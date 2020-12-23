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
% DateTime   : Thu Dec  3 12:40:47 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 128 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  223 ( 368 expanded)
%              Number of equality atoms :  144 ( 281 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f366,plain,(
    $false ),
    inference(subsumption_resolution,[],[f365,f93])).

fof(f93,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(superposition,[],[f90,f41])).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f90,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f76,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f76,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).

fof(f33,plain,(
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

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f365,plain,(
    ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f363,f159])).

fof(f159,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f150,f36])).

fof(f36,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK0 != k1_tarski(sK1)
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( sK0 != k1_tarski(sK1)
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

fof(f150,plain,
    ( k1_xboole_0 = sK0
    | r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f55,f35])).

fof(f35,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f363,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ r2_hidden(sK1,k1_tarski(sK1)) ),
    inference(resolution,[],[f343,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f343,plain,(
    r2_hidden(sK1,k5_xboole_0(sK0,k1_tarski(sK1))) ),
    inference(subsumption_resolution,[],[f334,f232])).

fof(f232,plain,(
    k1_xboole_0 != k5_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(subsumption_resolution,[],[f227,f144])).

fof(f144,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(subsumption_resolution,[],[f143,f37])).

fof(f37,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f143,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ r1_tarski(k1_tarski(sK1),sK0) ),
    inference(resolution,[],[f51,f100])).

fof(f100,plain,(
    r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(trivial_inequality_removal,[],[f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f52,f35])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f227,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k1_tarski(sK1))
    | r1_tarski(k1_tarski(sK1),sK0) ),
    inference(superposition,[],[f52,f192])).

fof(f192,plain,(
    k5_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(k1_tarski(sK1),sK0) ),
    inference(superposition,[],[f161,f79])).

fof(f79,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f43,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f161,plain,(
    k5_xboole_0(sK0,k1_tarski(sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(sK1),sK0)) ),
    inference(superposition,[],[f48,f35])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f334,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK1,k5_xboole_0(sK0,k1_tarski(sK1))) ),
    inference(superposition,[],[f321,f55])).

fof(f321,plain,(
    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k1_tarski(sK1)),k1_tarski(sK1)) ),
    inference(superposition,[],[f82,f231])).

fof(f231,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK0,k5_xboole_0(sK0,k1_tarski(sK1))) ),
    inference(forward_demodulation,[],[f224,f133])).

fof(f133,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f126,f43])).

fof(f126,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f118,f39])).

fof(f118,plain,(
    k2_xboole_0(k1_tarski(sK1),sK0) = k2_xboole_0(k1_tarski(sK1),k1_xboole_0) ),
    inference(superposition,[],[f46,f35])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f224,plain,(
    k2_xboole_0(sK0,k1_tarski(sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK0,k1_tarski(sK1))) ),
    inference(superposition,[],[f46,f192])).

fof(f82,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f42,f43])).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.50  % (2077)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (2076)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (2072)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.50  % (2071)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.51  % (2080)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.51  % (2100)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (2074)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (2087)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.19/0.51  % (2079)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.51  % (2090)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.51  % (2073)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (2092)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.52  % (2081)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.19/0.52  % (2093)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (2094)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (2087)Refutation not found, incomplete strategy% (2087)------------------------------
% 0.19/0.52  % (2087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (2086)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (2087)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (2087)Memory used [KB]: 10618
% 0.19/0.52  % (2087)Time elapsed: 0.122 s
% 0.19/0.52  % (2087)------------------------------
% 0.19/0.52  % (2087)------------------------------
% 0.19/0.52  % (2078)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.52  % (2084)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.52  % (2085)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.52  % (2089)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.53  % (2082)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.53  % (2097)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.53  % (2098)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.53  % (2075)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.53  % (2100)Refutation not found, incomplete strategy% (2100)------------------------------
% 0.19/0.53  % (2100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2100)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (2100)Memory used [KB]: 1663
% 0.19/0.53  % (2100)Time elapsed: 0.134 s
% 0.19/0.53  % (2100)------------------------------
% 0.19/0.53  % (2100)------------------------------
% 0.19/0.53  % (2095)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.19/0.53  % (2080)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.53  % SZS output start Proof for theBenchmark
% 0.19/0.53  fof(f366,plain,(
% 0.19/0.53    $false),
% 0.19/0.53    inference(subsumption_resolution,[],[f365,f93])).
% 0.19/0.53  fof(f93,plain,(
% 0.19/0.53    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.19/0.53    inference(superposition,[],[f90,f41])).
% 0.19/0.53  fof(f41,plain,(
% 0.19/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f14])).
% 0.19/0.53  fof(f14,axiom,(
% 0.19/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.53  fof(f90,plain,(
% 0.19/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.19/0.53    inference(superposition,[],[f76,f44])).
% 0.19/0.53  fof(f44,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f15])).
% 0.19/0.53  fof(f15,axiom,(
% 0.19/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.53  fof(f76,plain,(
% 0.19/0.53    ( ! [X2,X5,X1] : (r2_hidden(X5,k1_enumset1(X5,X1,X2))) )),
% 0.19/0.53    inference(equality_resolution,[],[f75])).
% 0.19/0.53  fof(f75,plain,(
% 0.19/0.53    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k1_enumset1(X5,X1,X2) != X3) )),
% 0.19/0.53    inference(equality_resolution,[],[f62])).
% 0.19/0.53  fof(f62,plain,(
% 0.19/0.53    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.19/0.53    inference(cnf_transformation,[],[f34])).
% 0.19/0.53  fof(f34,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f32,f33])).
% 0.19/0.53  fof(f33,plain,(
% 0.19/0.53    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK2(X0,X1,X2,X3) != X2 & sK2(X0,X1,X2,X3) != X1 & sK2(X0,X1,X2,X3) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3),X3)) & (sK2(X0,X1,X2,X3) = X2 | sK2(X0,X1,X2,X3) = X1 | sK2(X0,X1,X2,X3) = X0 | r2_hidden(sK2(X0,X1,X2,X3),X3))))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f32,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.53    inference(rectify,[],[f31])).
% 0.19/0.53  fof(f31,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.53    inference(flattening,[],[f30])).
% 0.19/0.53  fof(f30,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.19/0.53    inference(nnf_transformation,[],[f22])).
% 0.19/0.53  fof(f22,plain,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.19/0.53    inference(ennf_transformation,[],[f13])).
% 0.19/0.53  fof(f13,axiom,(
% 0.19/0.53    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.19/0.53  fof(f365,plain,(
% 0.19/0.53    ~r2_hidden(sK1,k1_tarski(sK1))),
% 0.19/0.53    inference(subsumption_resolution,[],[f363,f159])).
% 0.19/0.53  fof(f159,plain,(
% 0.19/0.53    r2_hidden(sK1,sK0)),
% 0.19/0.53    inference(subsumption_resolution,[],[f150,f36])).
% 0.19/0.53  fof(f36,plain,(
% 0.19/0.53    k1_xboole_0 != sK0),
% 0.19/0.53    inference(cnf_transformation,[],[f24])).
% 0.19/0.53  fof(f24,plain,(
% 0.19/0.53    sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.19/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f23])).
% 0.19/0.53  fof(f23,plain,(
% 0.19/0.53    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.19/0.53    introduced(choice_axiom,[])).
% 0.19/0.53  fof(f20,plain,(
% 0.19/0.53    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.19/0.53    inference(ennf_transformation,[],[f19])).
% 0.19/0.53  fof(f19,negated_conjecture,(
% 0.19/0.53    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.19/0.53    inference(negated_conjecture,[],[f18])).
% 0.19/0.53  fof(f18,conjecture,(
% 0.19/0.53    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).
% 0.19/0.53  fof(f150,plain,(
% 0.19/0.53    k1_xboole_0 = sK0 | r2_hidden(sK1,sK0)),
% 0.19/0.53    inference(superposition,[],[f55,f35])).
% 0.19/0.53  fof(f35,plain,(
% 0.19/0.53    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.19/0.53    inference(cnf_transformation,[],[f24])).
% 0.19/0.53  fof(f55,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f28])).
% 0.19/0.53  fof(f28,plain,(
% 0.19/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.19/0.53    inference(nnf_transformation,[],[f17])).
% 0.19/0.53  fof(f17,axiom,(
% 0.19/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.19/0.53  fof(f363,plain,(
% 0.19/0.53    ~r2_hidden(sK1,sK0) | ~r2_hidden(sK1,k1_tarski(sK1))),
% 0.19/0.53    inference(resolution,[],[f343,f58])).
% 0.19/0.53  fof(f58,plain,(
% 0.19/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f29])).
% 0.19/0.53  fof(f29,plain,(
% 0.19/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.19/0.53    inference(nnf_transformation,[],[f21])).
% 0.19/0.53  fof(f21,plain,(
% 0.19/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.19/0.53    inference(ennf_transformation,[],[f3])).
% 0.19/0.53  fof(f3,axiom,(
% 0.19/0.53    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.19/0.53  fof(f343,plain,(
% 0.19/0.53    r2_hidden(sK1,k5_xboole_0(sK0,k1_tarski(sK1)))),
% 0.19/0.53    inference(subsumption_resolution,[],[f334,f232])).
% 0.19/0.53  fof(f232,plain,(
% 0.19/0.53    k1_xboole_0 != k5_xboole_0(sK0,k1_tarski(sK1))),
% 0.19/0.53    inference(subsumption_resolution,[],[f227,f144])).
% 0.19/0.53  fof(f144,plain,(
% 0.19/0.53    ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.19/0.53    inference(subsumption_resolution,[],[f143,f37])).
% 0.19/0.53  fof(f37,plain,(
% 0.19/0.53    sK0 != k1_tarski(sK1)),
% 0.19/0.53    inference(cnf_transformation,[],[f24])).
% 0.19/0.53  fof(f143,plain,(
% 0.19/0.53    sK0 = k1_tarski(sK1) | ~r1_tarski(k1_tarski(sK1),sK0)),
% 0.19/0.53    inference(resolution,[],[f51,f100])).
% 0.19/0.53  fof(f100,plain,(
% 0.19/0.53    r1_tarski(sK0,k1_tarski(sK1))),
% 0.19/0.53    inference(trivial_inequality_removal,[],[f94])).
% 0.19/0.53  fof(f94,plain,(
% 0.19/0.53    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k1_tarski(sK1))),
% 0.19/0.53    inference(superposition,[],[f52,f35])).
% 0.19/0.53  fof(f52,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f27])).
% 0.19/0.53  fof(f27,plain,(
% 0.19/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.53    inference(nnf_transformation,[],[f5])).
% 0.19/0.53  fof(f5,axiom,(
% 0.19/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.53  fof(f51,plain,(
% 0.19/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f26])).
% 0.19/0.53  fof(f26,plain,(
% 0.19/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.53    inference(flattening,[],[f25])).
% 0.19/0.53  fof(f25,plain,(
% 0.19/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.53    inference(nnf_transformation,[],[f4])).
% 0.19/0.53  fof(f4,axiom,(
% 0.19/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.53  fof(f227,plain,(
% 0.19/0.53    k1_xboole_0 != k5_xboole_0(sK0,k1_tarski(sK1)) | r1_tarski(k1_tarski(sK1),sK0)),
% 0.19/0.53    inference(superposition,[],[f52,f192])).
% 0.19/0.53  fof(f192,plain,(
% 0.19/0.53    k5_xboole_0(sK0,k1_tarski(sK1)) = k4_xboole_0(k1_tarski(sK1),sK0)),
% 0.19/0.53    inference(superposition,[],[f161,f79])).
% 0.19/0.53  fof(f79,plain,(
% 0.19/0.53    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.19/0.53    inference(superposition,[],[f43,f39])).
% 0.19/0.53  fof(f39,plain,(
% 0.19/0.53    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.53    inference(cnf_transformation,[],[f7])).
% 0.19/0.53  fof(f7,axiom,(
% 0.19/0.53    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.53  fof(f43,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.53    inference(cnf_transformation,[],[f1])).
% 0.19/0.53  fof(f1,axiom,(
% 0.19/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.53  fof(f161,plain,(
% 0.19/0.53    k5_xboole_0(sK0,k1_tarski(sK1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(sK1),sK0))),
% 0.19/0.53    inference(superposition,[],[f48,f35])).
% 0.19/0.53  fof(f48,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f2])).
% 0.19/0.53  fof(f2,axiom,(
% 0.19/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.19/0.53  fof(f334,plain,(
% 0.19/0.53    k1_xboole_0 = k5_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK1,k5_xboole_0(sK0,k1_tarski(sK1)))),
% 0.19/0.53    inference(superposition,[],[f321,f55])).
% 0.19/0.53  fof(f321,plain,(
% 0.19/0.53    k1_xboole_0 = k4_xboole_0(k5_xboole_0(sK0,k1_tarski(sK1)),k1_tarski(sK1))),
% 0.19/0.53    inference(superposition,[],[f82,f231])).
% 0.19/0.53  fof(f231,plain,(
% 0.19/0.53    k1_tarski(sK1) = k2_xboole_0(sK0,k5_xboole_0(sK0,k1_tarski(sK1)))),
% 0.19/0.53    inference(forward_demodulation,[],[f224,f133])).
% 0.19/0.53  fof(f133,plain,(
% 0.19/0.53    k1_tarski(sK1) = k2_xboole_0(sK0,k1_tarski(sK1))),
% 0.19/0.53    inference(superposition,[],[f126,f43])).
% 0.19/0.53  fof(f126,plain,(
% 0.19/0.53    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),sK0)),
% 0.19/0.53    inference(forward_demodulation,[],[f118,f39])).
% 0.19/0.53  fof(f118,plain,(
% 0.19/0.53    k2_xboole_0(k1_tarski(sK1),sK0) = k2_xboole_0(k1_tarski(sK1),k1_xboole_0)),
% 0.19/0.53    inference(superposition,[],[f46,f35])).
% 0.19/0.53  fof(f46,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f9])).
% 0.19/0.53  fof(f9,axiom,(
% 0.19/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.19/0.53  fof(f224,plain,(
% 0.19/0.53    k2_xboole_0(sK0,k1_tarski(sK1)) = k2_xboole_0(sK0,k5_xboole_0(sK0,k1_tarski(sK1)))),
% 0.19/0.53    inference(superposition,[],[f46,f192])).
% 0.19/0.53  fof(f82,plain,(
% 0.19/0.53    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 0.19/0.53    inference(superposition,[],[f42,f43])).
% 0.19/0.53  fof(f42,plain,(
% 0.19/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.53    inference(cnf_transformation,[],[f11])).
% 0.19/0.53  fof(f11,axiom,(
% 0.19/0.53    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.19/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.19/0.53  % SZS output end Proof for theBenchmark
% 0.19/0.53  % (2080)------------------------------
% 0.19/0.53  % (2080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (2080)Termination reason: Refutation
% 0.19/0.53  
% 0.19/0.53  % (2080)Memory used [KB]: 1918
% 0.19/0.53  % (2080)Time elapsed: 0.138 s
% 0.19/0.53  % (2080)------------------------------
% 0.19/0.53  % (2080)------------------------------
% 0.19/0.53  % (2070)Success in time 0.178 s
%------------------------------------------------------------------------------
