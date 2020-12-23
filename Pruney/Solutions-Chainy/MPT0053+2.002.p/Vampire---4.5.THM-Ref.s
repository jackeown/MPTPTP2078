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
% DateTime   : Thu Dec  3 12:29:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 263 expanded)
%              Number of leaves         :   10 (  82 expanded)
%              Depth                    :   16
%              Number of atoms          :  142 ( 941 expanded)
%              Number of equality atoms :   28 ( 116 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f408,plain,(
    $false ),
    inference(subsumption_resolution,[],[f24,f407])).

fof(f407,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f71,f338])).

fof(f338,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(X3,X3) ),
    inference(resolution,[],[f310,f39])).

fof(f39,plain,(
    ! [X0,X1] : sP1(X0,X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X0,X1,X2) )
      & ( sP1(X0,X1,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f12,f11])).

fof(f11,plain,(
    ! [X1,X3,X0] :
      ( sP0(X1,X3,X0)
    <=> ( ~ r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP0(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ sP1(X1,X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f309,f89])).

fof(f89,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ sP1(X7,X8,X10)
      | X9 = X10
      | ~ sP1(X7,X8,X9) ) ),
    inference(superposition,[],[f38,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f309,plain,(
    ! [X7] : sP1(X7,X7,k1_xboole_0) ),
    inference(resolution,[],[f232,f246])).

fof(f246,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(resolution,[],[f225,f224])).

fof(f224,plain,(
    ! [X10,X9] : ~ r2_hidden(X10,k4_xboole_0(X9,X9)) ),
    inference(subsumption_resolution,[],[f184,f222])).

fof(f222,plain,(
    ! [X2,X3] : ~ sP0(X2,X3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f220,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( ~ r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X1,X3,X0] :
      ( ( sP0(X1,X3,X0)
        | r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( ~ r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP0(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f220,plain,(
    ! [X2,X3] :
      ( ~ sP0(X2,X3,k1_xboole_0)
      | r2_hidden(X3,X2) ) ),
    inference(resolution,[],[f207,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f207,plain,(
    ! [X6,X5] :
      ( sP0(X5,X6,X5)
      | ~ sP0(X5,X6,k1_xboole_0) ) ),
    inference(resolution,[],[f197,f186])).

fof(f186,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X15,k4_xboole_0(k1_xboole_0,X14))
      | sP0(X14,X15,X14) ) ),
    inference(superposition,[],[f173,f50])).

fof(f50,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5) ),
    inference(superposition,[],[f27,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X2))
      | sP0(X2,X0,X1) ) ),
    inference(resolution,[],[f30,f39])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | sP0(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f19])).

% (12162)Refutation not found, incomplete strategy% (12162)------------------------------
% (12162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (12162)Termination reason: Refutation not found, incomplete strategy

% (12162)Memory used [KB]: 6012
% (12162)Time elapsed: 0.103 s
fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ~ sP0(X1,sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sP0(X1,sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).

% (12162)------------------------------
% (12162)------------------------------
fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP0(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP0(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP0(X1,sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sP0(X1,sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP0(X1,X4,X0) )
            & ( sP0(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP0(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP0(X1,X3,X0) )
            & ( sP0(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k4_xboole_0(X2,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f31,f39])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X1,X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X10,k4_xboole_0(X9,X9))
      | sP0(X9,X10,k1_xboole_0) ) ),
    inference(superposition,[],[f173,f50])).

fof(f225,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f222,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f232,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK4(X6,X6,X7),X7)
      | sP1(X6,X6,X7) ) ),
    inference(resolution,[],[f32,f223])).

fof(f223,plain,(
    ! [X4,X3] : ~ sP0(X3,X4,X3) ),
    inference(subsumption_resolution,[],[f206,f222])).

fof(f206,plain,(
    ! [X4,X3] :
      ( sP0(X3,X4,k1_xboole_0)
      | ~ sP0(X3,X4,X3) ) ),
    inference(resolution,[],[f197,f184])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,sK4(X0,X1,X2),X0)
      | sP1(X0,X1,X2)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f24,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))
   => k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:00:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.47  % (12160)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (12161)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (12159)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (12168)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (12168)Refutation not found, incomplete strategy% (12168)------------------------------
% 0.21/0.49  % (12168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12168)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12168)Memory used [KB]: 10490
% 0.21/0.49  % (12168)Time elapsed: 0.082 s
% 0.21/0.49  % (12168)------------------------------
% 0.21/0.49  % (12168)------------------------------
% 0.21/0.50  % (12172)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (12162)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (12180)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (12161)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f24,f407])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.21/0.51    inference(forward_demodulation,[],[f71,f338])).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3)) )),
% 0.21/0.51    inference(resolution,[],[f310,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP1(X0,X1,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) & (sP1(X0,X1,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X0,X1,X2))),
% 0.21/0.51    inference(definition_folding,[],[f2,f12,f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X1,X3,X0] : (sP0(X1,X3,X0) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (sP1(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP0(X1,X3,X0)))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP1(X1,X1,X0) | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(resolution,[],[f309,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X10,X8,X7,X9] : (~sP1(X7,X8,X10) | X9 = X10 | ~sP1(X7,X8,X9)) )),
% 0.21/0.51    inference(superposition,[],[f38,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~sP1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    ( ! [X7] : (sP1(X7,X7,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f232,f246])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f225,f224])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ( ! [X10,X9] : (~r2_hidden(X10,k4_xboole_0(X9,X9))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f184,f222])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~sP0(X2,X3,k1_xboole_0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f220,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((~r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X1,X3,X0] : ((sP0(X1,X3,X0) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP0(X1,X3,X0)))),
% 0.21/0.51    inference(nnf_transformation,[],[f11])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~sP0(X2,X3,k1_xboole_0) | r2_hidden(X3,X2)) )),
% 0.21/0.51    inference(resolution,[],[f207,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ( ! [X6,X5] : (sP0(X5,X6,X5) | ~sP0(X5,X6,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f197,f186])).
% 0.21/0.51  fof(f186,plain,(
% 0.21/0.51    ( ! [X14,X15] : (~r2_hidden(X15,k4_xboole_0(k1_xboole_0,X14)) | sP0(X14,X15,X14)) )),
% 0.21/0.51    inference(superposition,[],[f173,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X5] : (k4_xboole_0(k1_xboole_0,X5) = k4_xboole_0(X5,X5)) )),
% 0.21/0.51    inference(superposition,[],[f27,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.51    inference(superposition,[],[f26,f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X2)) | sP0(X2,X0,X1)) )),
% 0.21/0.51    inference(resolution,[],[f30,f39])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X2) | sP0(X1,X4,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  % (12162)Refutation not found, incomplete strategy% (12162)------------------------------
% 0.21/0.51  % (12162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12162)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12162)Memory used [KB]: 6012
% 0.21/0.51  % (12162)Time elapsed: 0.103 s
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ((~sP0(X1,sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f18])).
% 0.21/0.51  % (12162)------------------------------
% 0.21/0.51  % (12162)------------------------------
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP0(X1,sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sP0(X1,sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP0(X1,X4,X0)) & (sP0(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : ((~sP0(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP0(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP0(X1,X3,X0)) & (sP0(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f12])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,k4_xboole_0(X2,X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f31,f39])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X1,X4,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f184,plain,(
% 0.21/0.51    ( ! [X10,X9] : (~r2_hidden(X10,k4_xboole_0(X9,X9)) | sP0(X9,X10,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f173,f50])).
% 0.21/0.51  fof(f225,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(resolution,[],[f222,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    ( ! [X6,X7] : (r2_hidden(sK4(X6,X6,X7),X7) | sP1(X6,X6,X7)) )),
% 0.21/0.51    inference(resolution,[],[f32,f223])).
% 0.21/0.51  fof(f223,plain,(
% 0.21/0.51    ( ! [X4,X3] : (~sP0(X3,X4,X3)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f206,f222])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X4,X3] : (sP0(X3,X4,k1_xboole_0) | ~sP0(X3,X4,X3)) )),
% 0.21/0.51    inference(resolution,[],[f197,f184])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X1,sK4(X0,X1,X2),X0) | sP1(X0,X1,X2) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X2,X3)) = k4_xboole_0(k2_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 0.21/0.51    inference(superposition,[],[f27,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f9,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1)) => k1_xboole_0 != k4_xboole_0(sK2,k2_xboole_0(sK2,sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1] : k1_xboole_0 != k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12161)------------------------------
% 0.21/0.51  % (12161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12161)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12161)Memory used [KB]: 6268
% 0.21/0.51  % (12161)Time elapsed: 0.103 s
% 0.21/0.51  % (12161)------------------------------
% 0.21/0.51  % (12161)------------------------------
% 0.21/0.51  % (12156)Success in time 0.159 s
%------------------------------------------------------------------------------
