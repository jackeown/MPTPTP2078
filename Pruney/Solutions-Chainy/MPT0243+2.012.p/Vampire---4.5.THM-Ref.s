%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 179 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  224 ( 616 expanded)
%              Number of equality atoms :   92 ( 108 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(subsumption_resolution,[],[f136,f93])).

fof(f93,plain,(
    ~ r1_tarski(k1_tarski(sK1),sK2) ),
    inference(subsumption_resolution,[],[f92,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f92,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f89,f82])).

fof(f82,plain,(
    r1_tarski(k1_tarski(sK0),sK2) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f81,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | r1_tarski(k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f28,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f28,plain,
    ( r2_hidden(sK0,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

% (16094)Refutation not found, incomplete strategy% (16094)------------------------------
% (16094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f21,plain,
    ( ( ~ r2_hidden(sK1,sK2)
      | ~ r2_hidden(sK0,sK2)
      | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
    & ( ( r2_hidden(sK1,sK2)
        & r2_hidden(sK0,sK2) )
      | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(X1,X2)
          | ~ r2_hidden(X0,X2)
          | ~ r1_tarski(k2_tarski(X0,X1),X2) )
        & ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X2) )
          | r1_tarski(k2_tarski(X0,X1),X2) ) )
   => ( ( ~ r2_hidden(sK1,sK2)
        | ~ r2_hidden(sK0,sK2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) )
      & ( ( r2_hidden(sK1,sK2)
          & r2_hidden(sK0,sK2) )
        | r1_tarski(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <~> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),X2)
      <=> ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f89,plain,
    ( ~ r1_tarski(k1_tarski(sK1),sK2)
    | ~ r1_tarski(k1_tarski(sK0),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f41,f85])).

fof(f85,plain,
    ( ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f48,f83])).

fof(f83,plain,(
    r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f82,f39])).

fof(f48,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f30,f45])).

fof(f30,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK0,sK2)
    | ~ r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

% (16116)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f136,plain,(
    r1_tarski(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f134,f94])).

fof(f94,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(subsumption_resolution,[],[f80,f93])).

fof(f80,plain,
    ( r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)
    | r1_tarski(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f29,f45])).

fof(f29,plain,
    ( r2_hidden(sK1,sK2)
    | r1_tarski(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2)
      | r1_tarski(k1_tarski(X1),X2) ) ),
    inference(superposition,[],[f133,f60])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f45,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f133,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tarski(k2_enumset1(X5,X5,X6,X4),X7)
      | r1_tarski(k1_tarski(X4),X7) ) ),
    inference(superposition,[],[f42,f75])).

fof(f75,plain,(
    ! [X4,X5,X3] : k2_enumset1(X4,X4,X5,X3) = k2_xboole_0(k1_tarski(X3),k2_enumset1(X4,X4,X5,X3)) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f68,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_tarski(X0),k2_enumset1(X1,X1,X2,X0)) ),
    inference(resolution,[],[f62,f40])).

fof(f62,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f34,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

% (16111)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:53:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (16096)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (16120)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (16101)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (16104)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (16097)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (16092)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (16106)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (16093)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (16113)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (16114)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (16108)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (16121)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (16097)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (16114)Refutation not found, incomplete strategy% (16114)------------------------------
% 0.21/0.53  % (16114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16095)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (16114)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16114)Memory used [KB]: 10618
% 0.21/0.53  % (16114)Time elapsed: 0.089 s
% 0.21/0.53  % (16114)------------------------------
% 0.21/0.53  % (16114)------------------------------
% 0.21/0.53  % (16100)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (16107)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (16098)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (16094)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (16102)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (16119)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (16102)Refutation not found, incomplete strategy% (16102)------------------------------
% 0.21/0.53  % (16102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16102)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16102)Memory used [KB]: 10618
% 0.21/0.53  % (16102)Time elapsed: 0.134 s
% 0.21/0.53  % (16102)------------------------------
% 0.21/0.53  % (16102)------------------------------
% 1.41/0.54  % (16115)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.54  % SZS output start Proof for theBenchmark
% 1.41/0.54  fof(f137,plain,(
% 1.41/0.54    $false),
% 1.41/0.54    inference(subsumption_resolution,[],[f136,f93])).
% 1.41/0.54  fof(f93,plain,(
% 1.41/0.54    ~r1_tarski(k1_tarski(sK1),sK2)),
% 1.41/0.54    inference(subsumption_resolution,[],[f92,f39])).
% 1.41/0.54  fof(f39,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f27])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.41/0.54    inference(nnf_transformation,[],[f8])).
% 1.41/0.54  fof(f8,axiom,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.54  fof(f92,plain,(
% 1.41/0.54    ~r1_tarski(k1_tarski(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 1.41/0.54    inference(subsumption_resolution,[],[f89,f82])).
% 1.41/0.54  fof(f82,plain,(
% 1.41/0.54    r1_tarski(k1_tarski(sK0),sK2)),
% 1.41/0.54    inference(subsumption_resolution,[],[f81,f42])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f16])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.41/0.54    inference(ennf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.41/0.54  fof(f81,plain,(
% 1.41/0.54    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | r1_tarski(k1_tarski(sK0),sK2)),
% 1.41/0.54    inference(resolution,[],[f50,f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f27])).
% 1.41/0.54  fof(f50,plain,(
% 1.41/0.54    r2_hidden(sK0,sK2) | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.41/0.54    inference(definition_unfolding,[],[f28,f45])).
% 1.41/0.54  fof(f45,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.41/0.54    inference(cnf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    r2_hidden(sK0,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  % (16094)Refutation not found, incomplete strategy% (16094)------------------------------
% 1.41/0.54  % (16094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    (~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2))) => ((~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)) & ((r2_hidden(sK1,sK2) & r2_hidden(sK0,sK2)) | r1_tarski(k2_tarski(sK0,sK1),sK2)))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    ? [X0,X1,X2] : ((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.41/0.54    inference(flattening,[],[f18])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    ? [X0,X1,X2] : (((~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.41/0.54    inference(nnf_transformation,[],[f12])).
% 1.41/0.54  fof(f12,plain,(
% 1.41/0.54    ? [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <~> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.54    inference(ennf_transformation,[],[f11])).
% 1.41/0.54  fof(f11,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.54    inference(negated_conjecture,[],[f10])).
% 1.41/0.54  fof(f10,conjecture,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.41/0.54  fof(f89,plain,(
% 1.41/0.54    ~r1_tarski(k1_tarski(sK1),sK2) | ~r1_tarski(k1_tarski(sK0),sK2) | ~r2_hidden(sK1,sK2)),
% 1.41/0.54    inference(resolution,[],[f41,f85])).
% 1.41/0.54  fof(f85,plain,(
% 1.41/0.54    ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | ~r2_hidden(sK1,sK2)),
% 1.41/0.54    inference(subsumption_resolution,[],[f48,f83])).
% 1.41/0.54  fof(f83,plain,(
% 1.41/0.54    r2_hidden(sK0,sK2)),
% 1.41/0.54    inference(resolution,[],[f82,f39])).
% 1.41/0.54  fof(f48,plain,(
% 1.41/0.54    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.41/0.54    inference(definition_unfolding,[],[f30,f45])).
% 1.41/0.54  fof(f30,plain,(
% 1.41/0.54    ~r2_hidden(sK1,sK2) | ~r2_hidden(sK0,sK2) | ~r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  % (16116)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.41/0.54  fof(f41,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f15])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.41/0.54    inference(flattening,[],[f14])).
% 1.41/0.54  fof(f14,plain,(
% 1.41/0.54    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.41/0.54    inference(ennf_transformation,[],[f3])).
% 1.41/0.54  fof(f3,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.41/0.54  fof(f136,plain,(
% 1.41/0.54    r1_tarski(k1_tarski(sK1),sK2)),
% 1.41/0.54    inference(resolution,[],[f134,f94])).
% 1.41/0.54  fof(f94,plain,(
% 1.41/0.54    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.41/0.54    inference(subsumption_resolution,[],[f80,f93])).
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) | r1_tarski(k1_tarski(sK1),sK2)),
% 1.41/0.54    inference(resolution,[],[f49,f40])).
% 1.41/0.54  fof(f49,plain,(
% 1.41/0.54    r2_hidden(sK1,sK2) | r1_tarski(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 1.41/0.54    inference(definition_unfolding,[],[f29,f45])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    r2_hidden(sK1,sK2) | r1_tarski(k2_tarski(sK0,sK1),sK2)),
% 1.41/0.54    inference(cnf_transformation,[],[f21])).
% 1.41/0.54  fof(f134,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),X2) | r1_tarski(k1_tarski(X1),X2)) )),
% 1.41/0.54    inference(superposition,[],[f133,f60])).
% 1.41/0.54  fof(f60,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.41/0.54    inference(definition_unfolding,[],[f46,f45,f47])).
% 1.41/0.54  fof(f47,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f6])).
% 1.41/0.54  fof(f6,axiom,(
% 1.41/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.54  fof(f133,plain,(
% 1.41/0.54    ( ! [X6,X4,X7,X5] : (~r1_tarski(k2_enumset1(X5,X5,X6,X4),X7) | r1_tarski(k1_tarski(X4),X7)) )),
% 1.41/0.54    inference(superposition,[],[f42,f75])).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    ( ! [X4,X5,X3] : (k2_enumset1(X4,X4,X5,X3) = k2_xboole_0(k1_tarski(X3),k2_enumset1(X4,X4,X5,X3))) )),
% 1.41/0.54    inference(resolution,[],[f68,f43])).
% 1.41/0.54  fof(f43,plain,(
% 1.41/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.41/0.54    inference(cnf_transformation,[],[f17])).
% 1.41/0.54  fof(f17,plain,(
% 1.41/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.41/0.54    inference(ennf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.41/0.54  fof(f68,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_tarski(X0),k2_enumset1(X1,X1,X2,X0))) )),
% 1.41/0.54    inference(resolution,[],[f62,f40])).
% 1.41/0.54  fof(f62,plain,(
% 1.41/0.54    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.41/0.54    inference(equality_resolution,[],[f61])).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.41/0.54    inference(equality_resolution,[],[f55])).
% 1.41/0.54  fof(f55,plain,(
% 1.41/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.41/0.54    inference(definition_unfolding,[],[f34,f47])).
% 1.41/0.54  fof(f34,plain,(
% 1.41/0.54    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.54    inference(cnf_transformation,[],[f26])).
% 1.41/0.54  fof(f26,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.41/0.54  fof(f25,plain,(
% 1.41/0.54    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 1.41/0.54    introduced(choice_axiom,[])).
% 1.41/0.54  fof(f24,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.54    inference(rectify,[],[f23])).
% 1.41/0.54  fof(f23,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.54    inference(flattening,[],[f22])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.41/0.54    inference(nnf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.41/0.54    inference(ennf_transformation,[],[f4])).
% 1.41/0.54  fof(f4,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.41/0.54  % (16111)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (16097)------------------------------
% 1.41/0.54  % (16097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (16097)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (16097)Memory used [KB]: 6268
% 1.41/0.54  % (16097)Time elapsed: 0.114 s
% 1.41/0.54  % (16097)------------------------------
% 1.41/0.54  % (16097)------------------------------
% 1.41/0.54  % (16091)Success in time 0.182 s
%------------------------------------------------------------------------------
