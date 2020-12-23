%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:02 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 338 expanded)
%              Number of leaves         :   31 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  460 ( 887 expanded)
%              Number of equality atoms :  191 ( 397 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f140,f147,f169,f255,f257,f282,f283,f451])).

fof(f451,plain,(
    ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl8_6 ),
    inference(resolution,[],[f427,f120])).

fof(f120,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP1(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f427,plain,
    ( ! [X0] : ~ sP1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_6 ),
    inference(resolution,[],[f423,f401])).

fof(f401,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f400])).

fof(f400,plain,(
    ! [X0] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f111,f109])).

fof(f109,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f111,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f106,f61,f106])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f105])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f82,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f83,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f84,f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f83,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f82,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f423,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ sP1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) )
    | ~ spl8_6 ),
    inference(resolution,[],[f415,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | ~ sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | r2_hidden(X10,X8) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).

fof(f47,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

% (7337)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (7340)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (7320)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (7331)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (7326)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (7333)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (7341)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (7328)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (7321)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (7318)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (7323)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (7323)Refutation not found, incomplete strategy% (7323)------------------------------
% (7323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7323)Termination reason: Refutation not found, incomplete strategy

% (7323)Memory used [KB]: 10746
% (7323)Time elapsed: 0.146 s
% (7323)------------------------------
% (7323)------------------------------
% (7334)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (7336)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (7332)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f415,plain,
    ( sP2(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0)
    | ~ spl8_6 ),
    inference(superposition,[],[f128,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl8_6
  <=> k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f128,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP2(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f31,f35,f34])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).

fof(f283,plain,
    ( ~ spl8_4
    | spl8_5
    | spl8_6 ),
    inference(avatar_split_clause,[],[f243,f162,f158,f154])).

fof(f154,plain,
    ( spl8_4
  <=> v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f158,plain,
    ( spl8_5
  <=> sK3 = k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f243,plain,
    ( k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK3 = k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(resolution,[],[f107,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | k1_relset_1(X1,X2,X0) = X1
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f70,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f32])).

fof(f32,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f107,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    inference(definition_unfolding,[],[f55,f106])).

fof(f55,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK4 != k1_funct_1(sK6,sK5)
    & r2_hidden(sK5,sK3)
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
    & v1_funct_2(sK6,sK3,k1_tarski(sK4))
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(X3,X2) != X1
        & r2_hidden(X2,X0)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
   => ( sK4 != k1_funct_1(sK6,sK5)
      & r2_hidden(sK5,sK3)
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))
      & v1_funct_2(sK6,sK3,k1_tarski(sK4))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(X3,X2) != X1
      & r2_hidden(X2,X0)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
      & v1_funct_2(X3,X0,k1_tarski(X1))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
          & v1_funct_2(X3,X0,k1_tarski(X1))
          & v1_funct_1(X3) )
       => ( r2_hidden(X2,X0)
         => k1_funct_1(X3,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1))))
        & v1_funct_2(X3,X0,k1_tarski(X1))
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => k1_funct_1(X3,X2) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

fof(f282,plain,
    ( ~ spl8_3
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f279])).

fof(f279,plain,
    ( sK4 != sK4
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(superposition,[],[f57,f276])).

fof(f276,plain,
    ( sK4 = k1_funct_1(sK6,sK5)
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(resolution,[],[f275,f56])).

fof(f56,plain,(
    r2_hidden(sK5,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f275,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK3)
        | sK4 = k1_funct_1(sK6,X2) )
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f274,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f274,plain,
    ( ! [X2] :
        ( sK4 = k2_mcart_1(k4_tarski(X2,k1_funct_1(sK6,X2)))
        | ~ r2_hidden(X2,sK3) )
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(resolution,[],[f272,f258])).

fof(f258,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
        | ~ r2_hidden(X0,sK3) )
    | ~ spl8_3
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f146,f253])).

fof(f253,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl8_14
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f146,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl8_3
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f272,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK6)
      | k2_mcart_1(X0) = sK4 ) ),
    inference(resolution,[],[f150,f107])).

fof(f150,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | ~ r2_hidden(X0,X2)
      | k2_mcart_1(X0) = X1 ) ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))
      | k2_mcart_1(X0) = X2 ) ),
    inference(definition_unfolding,[],[f78,f106])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_mcart_1(X0) = X2
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))
     => ( k2_mcart_1(X0) = X2
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

fof(f57,plain,(
    sK4 != k1_funct_1(sK6,sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f257,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | spl8_13 ),
    inference(resolution,[],[f249,f107])).

fof(f249,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl8_13
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f255,plain,
    ( ~ spl8_13
    | spl8_14
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f245,f158,f251,f247])).

fof(f245,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))
    | ~ spl8_5 ),
    inference(superposition,[],[f69,f160])).

fof(f160,plain,
    ( sK3 = k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f158])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f169,plain,(
    spl8_4 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl8_4 ),
    inference(resolution,[],[f156,f108])).

fof(f108,plain,(
    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(definition_unfolding,[],[f54,f106])).

fof(f54,plain,(
    v1_funct_2(sK6,sK3,k1_tarski(sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f156,plain,
    ( ~ v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | spl8_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f147,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f143,f145,f131])).

fof(f131,plain,
    ( spl8_1
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK6))
      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
      | ~ v1_relat_1(sK6) ) ),
    inference(resolution,[],[f119,f53])).

fof(f53,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f140,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f138,f107])).

fof(f138,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_1 ),
    inference(resolution,[],[f133,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f133,plain,
    ( ~ v1_relat_1(sK6)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:03:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (7330)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.50  % (7322)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (7322)Refutation not found, incomplete strategy% (7322)------------------------------
% 0.22/0.50  % (7322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7322)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7322)Memory used [KB]: 10746
% 0.22/0.50  % (7322)Time elapsed: 0.099 s
% 0.22/0.50  % (7322)------------------------------
% 0.22/0.50  % (7322)------------------------------
% 0.22/0.51  % (7338)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (7324)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (7314)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (7335)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (7316)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (7315)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (7317)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.54  % (7313)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.55  % (7319)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.55  % (7312)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.55  % (7325)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.55  % (7339)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (7329)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (7329)Refutation not found, incomplete strategy% (7329)------------------------------
% 1.42/0.55  % (7329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (7329)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (7329)Memory used [KB]: 10618
% 1.42/0.55  % (7329)Time elapsed: 0.134 s
% 1.42/0.55  % (7329)------------------------------
% 1.42/0.55  % (7329)------------------------------
% 1.42/0.55  % (7327)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (7324)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % SZS output start Proof for theBenchmark
% 1.42/0.55  fof(f452,plain,(
% 1.42/0.55    $false),
% 1.42/0.55    inference(avatar_sat_refutation,[],[f140,f147,f169,f255,f257,f282,f283,f451])).
% 1.42/0.55  fof(f451,plain,(
% 1.42/0.55    ~spl8_6),
% 1.42/0.55    inference(avatar_contradiction_clause,[],[f434])).
% 1.42/0.55  fof(f434,plain,(
% 1.42/0.55    $false | ~spl8_6),
% 1.42/0.55    inference(resolution,[],[f427,f120])).
% 1.42/0.55  fof(f120,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP1(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.42/0.55    inference(equality_resolution,[],[f98])).
% 1.42/0.55  fof(f98,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 1.42/0.55    inference(cnf_transformation,[],[f51])).
% 1.42/0.55  fof(f51,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.42/0.55    inference(rectify,[],[f50])).
% 1.42/0.55  fof(f50,plain,(
% 1.42/0.55    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.42/0.55    inference(flattening,[],[f49])).
% 1.42/0.55  fof(f49,plain,(
% 1.42/0.55    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.42/0.55    inference(nnf_transformation,[],[f34])).
% 1.42/0.55  fof(f34,plain,(
% 1.42/0.55    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 1.42/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.42/0.55  fof(f427,plain,(
% 1.42/0.55    ( ! [X0] : (~sP1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ) | ~spl8_6),
% 1.42/0.55    inference(resolution,[],[f423,f401])).
% 1.42/0.55  fof(f401,plain,(
% 1.42/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f400])).
% 1.42/0.55  fof(f400,plain,(
% 1.42/0.55    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.42/0.55    inference(superposition,[],[f111,f109])).
% 1.42/0.55  fof(f109,plain,(
% 1.42/0.55    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.42/0.55    inference(definition_unfolding,[],[f58,f61])).
% 1.42/0.55  fof(f61,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.55    inference(cnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.55  fof(f58,plain,(
% 1.42/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.55    inference(cnf_transformation,[],[f2])).
% 1.42/0.55  fof(f2,axiom,(
% 1.42/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.42/0.55  fof(f111,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) | ~r2_hidden(X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f65,f106,f61,f106])).
% 1.42/0.55  fof(f106,plain,(
% 1.42/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f59,f105])).
% 1.42/0.55  fof(f105,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f60,f104])).
% 1.42/0.55  fof(f104,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f67,f103])).
% 1.42/0.55  fof(f103,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f82,f102])).
% 1.42/0.55  fof(f102,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f83,f101])).
% 1.42/0.55  fof(f101,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.55    inference(definition_unfolding,[],[f84,f85])).
% 1.42/0.55  fof(f85,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f9])).
% 1.42/0.55  fof(f9,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.42/0.55  fof(f84,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f8])).
% 1.42/0.55  fof(f8,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.42/0.55  fof(f83,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f7])).
% 1.42/0.55  fof(f7,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.42/0.55  fof(f82,plain,(
% 1.42/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f6])).
% 1.42/0.55  fof(f6,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.42/0.55  fof(f67,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f5])).
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.55  fof(f60,plain,(
% 1.42/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f4])).
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.55  fof(f59,plain,(
% 1.42/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f3])).
% 1.42/0.55  fof(f3,axiom,(
% 1.42/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.55  fof(f65,plain,(
% 1.42/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f39])).
% 1.42/0.55  fof(f39,plain,(
% 1.42/0.55    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 1.42/0.55    inference(nnf_transformation,[],[f10])).
% 1.42/0.55  fof(f10,axiom,(
% 1.42/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.42/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.42/0.55  fof(f423,plain,(
% 1.42/0.55    ( ! [X0] : (r2_hidden(X0,k1_xboole_0) | ~sP1(X0,sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ) | ~spl8_6),
% 1.42/0.55    inference(resolution,[],[f415,f87])).
% 1.42/0.55  fof(f87,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ~sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X10,X8)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f48])).
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.42/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f46,f47])).
% 1.42/0.55  fof(f47,plain,(
% 1.42/0.55    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP1(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK7(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.42/0.55    introduced(choice_axiom,[])).
% 1.42/0.55  % (7337)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.42/0.55  % (7340)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (7320)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (7331)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (7326)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.56  % (7333)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.56  % (7341)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.42/0.56  % (7328)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  % (7321)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (7318)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.56  % (7323)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.54/0.56  % (7323)Refutation not found, incomplete strategy% (7323)------------------------------
% 1.54/0.56  % (7323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (7323)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (7323)Memory used [KB]: 10746
% 1.54/0.56  % (7323)Time elapsed: 0.146 s
% 1.54/0.56  % (7323)------------------------------
% 1.54/0.56  % (7323)------------------------------
% 1.54/0.56  % (7334)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.56  % (7336)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.54/0.57  % (7332)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.57  fof(f46,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP1(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.54/0.57    inference(rectify,[],[f45])).
% 1.54/0.57  fof(f45,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.54/0.57    inference(nnf_transformation,[],[f35])).
% 1.54/0.57  fof(f35,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP1(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 1.54/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.54/0.57  fof(f415,plain,(
% 1.54/0.57    sP2(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4,k1_xboole_0) | ~spl8_6),
% 1.54/0.57    inference(superposition,[],[f128,f164])).
% 1.54/0.57  fof(f164,plain,(
% 1.54/0.57    k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | ~spl8_6),
% 1.54/0.57    inference(avatar_component_clause,[],[f162])).
% 1.54/0.57  fof(f162,plain,(
% 1.54/0.57    spl8_6 <=> k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.54/0.57  fof(f128,plain,(
% 1.54/0.57    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.54/0.57    inference(equality_resolution,[],[f99])).
% 1.54/0.57  fof(f99,plain,(
% 1.54/0.57    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.54/0.57    inference(cnf_transformation,[],[f52])).
% 1.54/0.57  fof(f52,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.54/0.57    inference(nnf_transformation,[],[f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP2(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 1.54/0.57    inference(definition_folding,[],[f31,f35,f34])).
% 1.54/0.57  fof(f31,plain,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.54/0.57    inference(ennf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,axiom,(
% 1.54/0.57    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_enumset1)).
% 1.54/0.57  fof(f283,plain,(
% 1.54/0.57    ~spl8_4 | spl8_5 | spl8_6),
% 1.54/0.57    inference(avatar_split_clause,[],[f243,f162,f158,f154])).
% 1.54/0.57  fof(f154,plain,(
% 1.54/0.57    spl8_4 <=> v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.54/0.57  fof(f158,plain,(
% 1.54/0.57    spl8_5 <=> sK3 = k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.54/0.57  fof(f243,plain,(
% 1.54/0.57    k1_xboole_0 = k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4) | sK3 = k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) | ~v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.54/0.57    inference(resolution,[],[f107,f149])).
% 1.54/0.57  fof(f149,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_xboole_0 = X2 | k1_relset_1(X1,X2,X0) = X1 | ~v1_funct_2(X0,X1,X2)) )),
% 1.54/0.57    inference(resolution,[],[f70,f74])).
% 1.54/0.57  fof(f74,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f42])).
% 1.54/0.57  fof(f42,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(nnf_transformation,[],[f33])).
% 1.54/0.57  fof(f33,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(definition_folding,[],[f27,f32])).
% 1.54/0.57  fof(f32,plain,(
% 1.54/0.57    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.54/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.57  fof(f27,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(flattening,[],[f26])).
% 1.54/0.57  fof(f26,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f18])).
% 1.54/0.57  fof(f18,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.54/0.57  fof(f70,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.54/0.57    inference(cnf_transformation,[],[f41])).
% 1.54/0.57  fof(f41,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.54/0.57    inference(rectify,[],[f40])).
% 1.54/0.57  fof(f40,plain,(
% 1.54/0.57    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.54/0.57    inference(nnf_transformation,[],[f32])).
% 1.54/0.57  fof(f107,plain,(
% 1.54/0.57    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.54/0.57    inference(definition_unfolding,[],[f55,f106])).
% 1.54/0.57  fof(f55,plain,(
% 1.54/0.57    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4))))),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f38,plain,(
% 1.54/0.57    sK4 != k1_funct_1(sK6,sK5) & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6)),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f22,f37])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (sK4 != k1_funct_1(sK6,sK5) & r2_hidden(sK5,sK3) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_tarski(sK4)))) & v1_funct_2(sK6,sK3,k1_tarski(sK4)) & v1_funct_1(sK6))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f22,plain,(
% 1.54/0.57    ? [X0,X1,X2,X3] : (k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3))),
% 1.54/0.57    inference(flattening,[],[f21])).
% 1.54/0.57  fof(f21,plain,(
% 1.54/0.57    ? [X0,X1,X2,X3] : ((k1_funct_1(X3,X2) != X1 & r2_hidden(X2,X0)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)))),
% 1.54/0.57    inference(ennf_transformation,[],[f20])).
% 1.54/0.57  fof(f20,negated_conjecture,(
% 1.54/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.54/0.57    inference(negated_conjecture,[],[f19])).
% 1.54/0.57  fof(f19,conjecture,(
% 1.54/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k1_tarski(X1)))) & v1_funct_2(X3,X0,k1_tarski(X1)) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => k1_funct_1(X3,X2) = X1))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).
% 1.54/0.57  fof(f282,plain,(
% 1.54/0.57    ~spl8_3 | ~spl8_14),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f281])).
% 1.54/0.57  fof(f281,plain,(
% 1.54/0.57    $false | (~spl8_3 | ~spl8_14)),
% 1.54/0.57    inference(trivial_inequality_removal,[],[f279])).
% 1.54/0.57  fof(f279,plain,(
% 1.54/0.57    sK4 != sK4 | (~spl8_3 | ~spl8_14)),
% 1.54/0.57    inference(superposition,[],[f57,f276])).
% 1.54/0.57  fof(f276,plain,(
% 1.54/0.57    sK4 = k1_funct_1(sK6,sK5) | (~spl8_3 | ~spl8_14)),
% 1.54/0.57    inference(resolution,[],[f275,f56])).
% 1.54/0.57  fof(f56,plain,(
% 1.54/0.57    r2_hidden(sK5,sK3)),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f275,plain,(
% 1.54/0.57    ( ! [X2] : (~r2_hidden(X2,sK3) | sK4 = k1_funct_1(sK6,X2)) ) | (~spl8_3 | ~spl8_14)),
% 1.54/0.57    inference(forward_demodulation,[],[f274,f63])).
% 1.54/0.57  fof(f63,plain,(
% 1.54/0.57    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.54/0.57    inference(cnf_transformation,[],[f17])).
% 1.54/0.57  fof(f17,axiom,(
% 1.54/0.57    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.54/0.57  fof(f274,plain,(
% 1.54/0.57    ( ! [X2] : (sK4 = k2_mcart_1(k4_tarski(X2,k1_funct_1(sK6,X2))) | ~r2_hidden(X2,sK3)) ) | (~spl8_3 | ~spl8_14)),
% 1.54/0.57    inference(resolution,[],[f272,f258])).
% 1.54/0.57  fof(f258,plain,(
% 1.54/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) | ~r2_hidden(X0,sK3)) ) | (~spl8_3 | ~spl8_14)),
% 1.54/0.57    inference(backward_demodulation,[],[f146,f253])).
% 1.54/0.57  fof(f253,plain,(
% 1.54/0.57    sK3 = k1_relat_1(sK6) | ~spl8_14),
% 1.54/0.57    inference(avatar_component_clause,[],[f251])).
% 1.54/0.57  fof(f251,plain,(
% 1.54/0.57    spl8_14 <=> sK3 = k1_relat_1(sK6)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.54/0.57  fof(f146,plain,(
% 1.54/0.57    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) | ~r2_hidden(X0,k1_relat_1(sK6))) ) | ~spl8_3),
% 1.54/0.57    inference(avatar_component_clause,[],[f145])).
% 1.54/0.57  fof(f145,plain,(
% 1.54/0.57    spl8_3 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.54/0.57  fof(f272,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,sK6) | k2_mcart_1(X0) = sK4) )),
% 1.54/0.57    inference(resolution,[],[f150,f107])).
% 1.54/0.57  fof(f150,plain,(
% 1.54/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | ~r2_hidden(X0,X2) | k2_mcart_1(X0) = X1) )),
% 1.54/0.57    inference(resolution,[],[f112,f64])).
% 1.54/0.57  fof(f64,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f23])).
% 1.54/0.57  fof(f23,plain,(
% 1.54/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.57    inference(ennf_transformation,[],[f12])).
% 1.54/0.57  fof(f12,axiom,(
% 1.54/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.54/0.57  fof(f112,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) | k2_mcart_1(X0) = X2) )),
% 1.54/0.57    inference(definition_unfolding,[],[f78,f106])).
% 1.54/0.57  fof(f78,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k2_mcart_1(X0) = X2 | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f28,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))))),
% 1.54/0.57    inference(ennf_transformation,[],[f16])).
% 1.54/0.57  fof(f16,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,k1_tarski(X2))) => (k2_mcart_1(X0) = X2 & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).
% 1.54/0.57  fof(f57,plain,(
% 1.54/0.57    sK4 != k1_funct_1(sK6,sK5)),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f257,plain,(
% 1.54/0.57    spl8_13),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f256])).
% 1.54/0.57  fof(f256,plain,(
% 1.54/0.57    $false | spl8_13),
% 1.54/0.57    inference(resolution,[],[f249,f107])).
% 1.54/0.57  fof(f249,plain,(
% 1.54/0.57    ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | spl8_13),
% 1.54/0.57    inference(avatar_component_clause,[],[f247])).
% 1.54/0.57  fof(f247,plain,(
% 1.54/0.57    spl8_13 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))))),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.54/0.57  fof(f255,plain,(
% 1.54/0.57    ~spl8_13 | spl8_14 | ~spl8_5),
% 1.54/0.57    inference(avatar_split_clause,[],[f245,f158,f251,f247])).
% 1.54/0.57  fof(f245,plain,(
% 1.54/0.57    sK3 = k1_relat_1(sK6) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)))) | ~spl8_5),
% 1.54/0.57    inference(superposition,[],[f69,f160])).
% 1.54/0.57  fof(f160,plain,(
% 1.54/0.57    sK3 = k1_relset_1(sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4),sK6) | ~spl8_5),
% 1.54/0.57    inference(avatar_component_clause,[],[f158])).
% 1.54/0.57  fof(f69,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f25])).
% 1.54/0.57  fof(f25,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f15])).
% 1.54/0.57  fof(f15,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.57  fof(f169,plain,(
% 1.54/0.57    spl8_4),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f167])).
% 1.54/0.57  fof(f167,plain,(
% 1.54/0.57    $false | spl8_4),
% 1.54/0.57    inference(resolution,[],[f156,f108])).
% 1.54/0.57  fof(f108,plain,(
% 1.54/0.57    v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4))),
% 1.54/0.57    inference(definition_unfolding,[],[f54,f106])).
% 1.54/0.57  fof(f54,plain,(
% 1.54/0.57    v1_funct_2(sK6,sK3,k1_tarski(sK4))),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f156,plain,(
% 1.54/0.57    ~v1_funct_2(sK6,sK3,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) | spl8_4),
% 1.54/0.57    inference(avatar_component_clause,[],[f154])).
% 1.54/0.57  fof(f147,plain,(
% 1.54/0.57    ~spl8_1 | spl8_3),
% 1.54/0.57    inference(avatar_split_clause,[],[f143,f145,f131])).
% 1.54/0.57  fof(f131,plain,(
% 1.54/0.57    spl8_1 <=> v1_relat_1(sK6)),
% 1.54/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.54/0.57  fof(f143,plain,(
% 1.54/0.57    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK6)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) | ~v1_relat_1(sK6)) )),
% 1.54/0.57    inference(resolution,[],[f119,f53])).
% 1.54/0.57  fof(f53,plain,(
% 1.54/0.57    v1_funct_1(sK6)),
% 1.54/0.57    inference(cnf_transformation,[],[f38])).
% 1.54/0.57  fof(f119,plain,(
% 1.54/0.57    ( ! [X2,X0] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~v1_relat_1(X2)) )),
% 1.54/0.57    inference(equality_resolution,[],[f81])).
% 1.54/0.57  fof(f81,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f44])).
% 1.54/0.57  fof(f44,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(flattening,[],[f43])).
% 1.54/0.57  fof(f43,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(nnf_transformation,[],[f30])).
% 1.54/0.57  fof(f30,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.54/0.57    inference(flattening,[],[f29])).
% 1.54/0.57  fof(f29,plain,(
% 1.54/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.54/0.57    inference(ennf_transformation,[],[f13])).
% 1.54/0.57  fof(f13,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.54/0.57  fof(f140,plain,(
% 1.54/0.57    spl8_1),
% 1.54/0.57    inference(avatar_contradiction_clause,[],[f139])).
% 1.54/0.57  fof(f139,plain,(
% 1.54/0.57    $false | spl8_1),
% 1.54/0.57    inference(resolution,[],[f138,f107])).
% 1.54/0.57  fof(f138,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl8_1),
% 1.54/0.57    inference(resolution,[],[f133,f68])).
% 1.54/0.57  fof(f68,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.57    inference(cnf_transformation,[],[f24])).
% 1.54/0.57  fof(f24,plain,(
% 1.54/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.57    inference(ennf_transformation,[],[f14])).
% 1.54/0.57  fof(f14,axiom,(
% 1.54/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.54/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.54/0.57  fof(f133,plain,(
% 1.54/0.57    ~v1_relat_1(sK6) | spl8_1),
% 1.54/0.57    inference(avatar_component_clause,[],[f131])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (7324)------------------------------
% 1.54/0.57  % (7324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (7324)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (7324)Memory used [KB]: 6396
% 1.54/0.57  % (7324)Time elapsed: 0.144 s
% 1.54/0.57  % (7324)------------------------------
% 1.54/0.57  % (7324)------------------------------
% 1.54/0.58  % (7311)Success in time 0.208 s
%------------------------------------------------------------------------------
