%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:20 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 594 expanded)
%              Number of leaves         :    7 ( 127 expanded)
%              Depth                    :   40
%              Number of atoms          :  198 (2187 expanded)
%              Number of equality atoms :  159 (1640 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f368,plain,(
    $false ),
    inference(subsumption_resolution,[],[f365,f228])).

fof(f228,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f21,f210])).

fof(f210,plain,(
    sK1 = sK3 ),
    inference(condensation,[],[f209])).

fof(f209,plain,(
    ! [X0] :
      ( sK1 = X0
      | sK1 = sK3 ) ),
    inference(condensation,[],[f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = sK3 ) ),
    inference(subsumption_resolution,[],[f191,f37])).

% (7206)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f37,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X1))
      | sK1 = X0
      | sK1 = X1
      | sK1 = sK3 ) ),
    inference(superposition,[],[f32,f183])).

fof(f183,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK1 = sK3 ),
    inference(forward_demodulation,[],[f179,f43])).

fof(f43,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(X2)) ),
    inference(resolution,[],[f25,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(superposition,[],[f37,f22])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

% (7199)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f179,plain,
    ( k1_tarski(sK1) = k3_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | sK1 = sK3 ),
    inference(superposition,[],[f161,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f161,plain,
    ( k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | sK1 = sK3 ),
    inference(superposition,[],[f44,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f143,f20])).

fof(f20,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f143,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3
    | sK0 = sK2 ),
    inference(resolution,[],[f109,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f32,f22])).

fof(f109,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(superposition,[],[f36,f99])).

fof(f99,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f90,f56])).

fof(f90,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK3))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | sK1 = sK3 ),
    inference(superposition,[],[f35,f83])).

fof(f83,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f79,f21])).

fof(f79,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK0 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f72,f32])).

fof(f72,plain,
    ( r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(superposition,[],[f35,f61])).

fof(f61,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f29])).

% (7198)Refutation not found, incomplete strategy% (7198)------------------------------
% (7198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X4,X3] : k1_tarski(X3) = k3_xboole_0(k1_tarski(X3),k2_tarski(X4,X3)) ),
    inference(resolution,[],[f25,f35])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f21,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f365,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f358,f56])).

fof(f358,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f36,f348])).

fof(f348,plain,(
    k2_tarski(sK0,sK1) = k1_tarski(sK1) ),
    inference(forward_demodulation,[],[f344,f44])).

fof(f344,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f335,f23])).

fof(f335,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f321,f22])).

fof(f321,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) ),
    inference(backward_demodulation,[],[f212,f319])).

fof(f319,plain,(
    sK1 = sK2 ),
    inference(condensation,[],[f318])).

fof(f318,plain,(
    ! [X0] :
      ( sK1 = X0
      | sK1 = sK2 ) ),
    inference(condensation,[],[f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = sK2 ) ),
    inference(subsumption_resolution,[],[f301,f37])).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X1))
      | sK1 = X0
      | sK1 = X1
      | sK1 = sK2 ) ),
    inference(superposition,[],[f32,f293])).

fof(f293,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK1 = sK2 ),
    inference(forward_demodulation,[],[f289,f43])).

fof(f289,plain,
    ( k1_tarski(sK1) = k3_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | sK1 = sK2 ),
    inference(superposition,[],[f280,f23])).

fof(f280,plain,
    ( k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | sK1 = sK2 ),
    inference(superposition,[],[f44,f266])).

% (7214)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f266,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f263,f228])).

fof(f263,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2
    | sK0 = sK1 ),
    inference(resolution,[],[f254,f56])).

fof(f254,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(superposition,[],[f36,f245])).

fof(f245,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f236,f56])).

fof(f236,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK2))
    | k2_tarski(sK0,sK1) = k1_tarski(sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(superposition,[],[f35,f222])).

fof(f222,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k1_tarski(sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(backward_demodulation,[],[f178,f210])).

fof(f178,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f170,f20])).

fof(f170,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK0 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f73,f32])).

fof(f73,plain,
    ( r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(superposition,[],[f36,f61])).

fof(f212,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK1)) ),
    inference(backward_demodulation,[],[f47,f210])).

fof(f47,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f25,f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (7190)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (7205)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (7218)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (7192)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (7197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (7205)Refutation not found, incomplete strategy% (7205)------------------------------
% 0.20/0.51  % (7205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7190)Refutation not found, incomplete strategy% (7190)------------------------------
% 0.20/0.51  % (7190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7190)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7190)Memory used [KB]: 1663
% 0.20/0.51  % (7190)Time elapsed: 0.101 s
% 0.20/0.51  % (7190)------------------------------
% 0.20/0.51  % (7190)------------------------------
% 0.20/0.51  % (7210)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (7202)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (7213)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (7205)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7205)Memory used [KB]: 6140
% 0.20/0.51  % (7205)Time elapsed: 0.105 s
% 0.20/0.51  % (7205)------------------------------
% 0.20/0.51  % (7205)------------------------------
% 0.20/0.51  % (7194)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (7195)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (7194)Refutation not found, incomplete strategy% (7194)------------------------------
% 0.20/0.51  % (7194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7194)Memory used [KB]: 6140
% 0.20/0.51  % (7194)Time elapsed: 0.114 s
% 0.20/0.51  % (7194)------------------------------
% 0.20/0.51  % (7194)------------------------------
% 0.20/0.52  % (7192)Refutation not found, incomplete strategy% (7192)------------------------------
% 0.20/0.52  % (7192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7192)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7192)Memory used [KB]: 10746
% 0.20/0.52  % (7192)Time elapsed: 0.109 s
% 0.20/0.52  % (7192)------------------------------
% 0.20/0.52  % (7192)------------------------------
% 0.20/0.52  % (7204)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.53  % (7215)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.53  % (7217)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.53  % (7212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.53  % (7191)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.53  % (7208)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.53  % (7203)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.53  % (7193)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.53  % (7198)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.53  % (7209)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (7197)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.29/0.53  % SZS output start Proof for theBenchmark
% 1.29/0.53  fof(f368,plain,(
% 1.29/0.53    $false),
% 1.29/0.53    inference(subsumption_resolution,[],[f365,f228])).
% 1.29/0.53  fof(f228,plain,(
% 1.29/0.53    sK0 != sK1),
% 1.29/0.53    inference(superposition,[],[f21,f210])).
% 1.29/0.53  fof(f210,plain,(
% 1.29/0.53    sK1 = sK3),
% 1.29/0.53    inference(condensation,[],[f209])).
% 1.29/0.53  fof(f209,plain,(
% 1.29/0.53    ( ! [X0] : (sK1 = X0 | sK1 = sK3) )),
% 1.29/0.53    inference(condensation,[],[f208])).
% 1.29/0.53  fof(f208,plain,(
% 1.29/0.53    ( ! [X0,X1] : (sK1 = X0 | sK1 = X1 | sK1 = sK3) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f191,f37])).
% 1.29/0.53  % (7206)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 1.29/0.53    inference(equality_resolution,[],[f28])).
% 1.29/0.53  fof(f28,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.29/0.53    inference(flattening,[],[f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.29/0.53    inference(nnf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.29/0.53    inference(ennf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.29/0.53  fof(f191,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) | sK1 = X0 | sK1 = X1 | sK1 = sK3) )),
% 1.29/0.53    inference(superposition,[],[f32,f183])).
% 1.29/0.53  fof(f183,plain,(
% 1.29/0.53    k1_xboole_0 = k1_tarski(sK1) | sK1 = sK3),
% 1.29/0.53    inference(forward_demodulation,[],[f179,f43])).
% 1.29/0.53  fof(f43,plain,(
% 1.29/0.53    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_tarski(X2))) )),
% 1.29/0.53    inference(resolution,[],[f25,f38])).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,k1_tarski(X0))) )),
% 1.29/0.53    inference(superposition,[],[f37,f22])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f3])).
% 1.29/0.53  fof(f3,axiom,(
% 1.29/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.53  fof(f25,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f12])).
% 1.29/0.53  % (7199)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.53  fof(f12,plain,(
% 1.29/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f2])).
% 1.29/0.53  fof(f2,axiom,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.29/0.53  fof(f179,plain,(
% 1.29/0.53    k1_tarski(sK1) = k3_xboole_0(k1_xboole_0,k1_tarski(sK1)) | sK1 = sK3),
% 1.29/0.53    inference(superposition,[],[f161,f23])).
% 1.29/0.53  fof(f23,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f1])).
% 1.29/0.53  fof(f1,axiom,(
% 1.29/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.29/0.53  fof(f161,plain,(
% 1.29/0.53    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_xboole_0) | sK1 = sK3),
% 1.29/0.53    inference(superposition,[],[f44,f146])).
% 1.29/0.53  fof(f146,plain,(
% 1.29/0.53    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 1.29/0.53    inference(subsumption_resolution,[],[f143,f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    sK0 != sK2),
% 1.29/0.53    inference(cnf_transformation,[],[f16])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.29/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f15])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f11,plain,(
% 1.29/0.53    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.29/0.53    inference(ennf_transformation,[],[f10])).
% 1.29/0.53  fof(f10,negated_conjecture,(
% 1.29/0.53    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.29/0.53    inference(negated_conjecture,[],[f9])).
% 1.29/0.53  fof(f9,conjecture,(
% 1.29/0.53    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.29/0.53  fof(f143,plain,(
% 1.29/0.53    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3 | sK0 = sK2),
% 1.29/0.53    inference(resolution,[],[f109,f56])).
% 1.29/0.53  fof(f56,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(X0)) | X0 = X1) )),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f55])).
% 1.29/0.53  fof(f55,plain,(
% 1.29/0.53    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 1.29/0.53    inference(superposition,[],[f32,f22])).
% 1.29/0.53  fof(f109,plain,(
% 1.29/0.53    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 1.29/0.53    inference(superposition,[],[f36,f99])).
% 1.29/0.53  fof(f99,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 1.29/0.53    inference(subsumption_resolution,[],[f90,f56])).
% 1.29/0.53  fof(f90,plain,(
% 1.29/0.53    r1_tarski(k1_tarski(sK1),k1_tarski(sK3)) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | sK1 = sK3),
% 1.29/0.53    inference(superposition,[],[f35,f83])).
% 1.29/0.53  fof(f83,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK3) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | sK1 = sK3),
% 1.29/0.53    inference(subsumption_resolution,[],[f79,f21])).
% 1.29/0.53  fof(f79,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3) | sK0 = sK3 | sK1 = sK3),
% 1.29/0.53    inference(resolution,[],[f72,f32])).
% 1.29/0.53  fof(f72,plain,(
% 1.29/0.53    r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1)) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 1.29/0.53    inference(superposition,[],[f35,f61])).
% 1.29/0.53  fof(f61,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 1.29/0.53    inference(resolution,[],[f27,f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.29/0.53    inference(cnf_transformation,[],[f16])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 1.29/0.53    inference(equality_resolution,[],[f30])).
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 1.29/0.53    inference(equality_resolution,[],[f29])).
% 1.29/0.53  % (7198)Refutation not found, incomplete strategy% (7198)------------------------------
% 1.29/0.53  % (7198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  fof(f29,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f44,plain,(
% 1.29/0.53    ( ! [X4,X3] : (k1_tarski(X3) = k3_xboole_0(k1_tarski(X3),k2_tarski(X4,X3))) )),
% 1.29/0.53    inference(resolution,[],[f25,f35])).
% 1.29/0.53  fof(f32,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 1.29/0.53    inference(cnf_transformation,[],[f14])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.29/0.53    inference(ennf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,axiom,(
% 1.29/0.53    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.29/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    sK0 != sK3),
% 1.29/0.53    inference(cnf_transformation,[],[f16])).
% 1.29/0.53  fof(f365,plain,(
% 1.29/0.53    sK0 = sK1),
% 1.29/0.53    inference(resolution,[],[f358,f56])).
% 1.29/0.53  fof(f358,plain,(
% 1.29/0.53    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 1.29/0.53    inference(superposition,[],[f36,f348])).
% 1.29/0.53  fof(f348,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k1_tarski(sK1)),
% 1.29/0.53    inference(forward_demodulation,[],[f344,f44])).
% 1.29/0.53  fof(f344,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k3_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 1.29/0.53    inference(superposition,[],[f335,f23])).
% 1.29/0.53  fof(f335,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))),
% 1.29/0.53    inference(forward_demodulation,[],[f321,f22])).
% 1.29/0.53  fof(f321,plain,(
% 1.29/0.53    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))),
% 1.29/0.53    inference(backward_demodulation,[],[f212,f319])).
% 1.29/0.53  fof(f319,plain,(
% 1.29/0.53    sK1 = sK2),
% 1.29/0.53    inference(condensation,[],[f318])).
% 1.29/0.53  fof(f318,plain,(
% 1.29/0.53    ( ! [X0] : (sK1 = X0 | sK1 = sK2) )),
% 1.29/0.53    inference(condensation,[],[f317])).
% 1.29/0.54  fof(f317,plain,(
% 1.29/0.54    ( ! [X0,X1] : (sK1 = X0 | sK1 = X1 | sK1 = sK2) )),
% 1.29/0.54    inference(subsumption_resolution,[],[f301,f37])).
% 1.29/0.54  fof(f301,plain,(
% 1.29/0.54    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) | sK1 = X0 | sK1 = X1 | sK1 = sK2) )),
% 1.29/0.54    inference(superposition,[],[f32,f293])).
% 1.29/0.54  fof(f293,plain,(
% 1.29/0.54    k1_xboole_0 = k1_tarski(sK1) | sK1 = sK2),
% 1.29/0.54    inference(forward_demodulation,[],[f289,f43])).
% 1.29/0.54  fof(f289,plain,(
% 1.29/0.54    k1_tarski(sK1) = k3_xboole_0(k1_xboole_0,k1_tarski(sK1)) | sK1 = sK2),
% 1.29/0.54    inference(superposition,[],[f280,f23])).
% 1.29/0.54  fof(f280,plain,(
% 1.29/0.54    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),k1_xboole_0) | sK1 = sK2),
% 1.29/0.54    inference(superposition,[],[f44,f266])).
% 1.29/0.54  % (7214)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.54  fof(f266,plain,(
% 1.29/0.54    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 1.29/0.54    inference(subsumption_resolution,[],[f263,f228])).
% 1.29/0.54  fof(f263,plain,(
% 1.29/0.54    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2 | sK0 = sK1),
% 1.29/0.54    inference(resolution,[],[f254,f56])).
% 1.29/0.54  fof(f254,plain,(
% 1.29/0.54    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 1.29/0.54    inference(superposition,[],[f36,f245])).
% 1.29/0.54  fof(f245,plain,(
% 1.29/0.54    k2_tarski(sK0,sK1) = k1_tarski(sK1) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 1.29/0.54    inference(subsumption_resolution,[],[f236,f56])).
% 1.29/0.54  fof(f236,plain,(
% 1.29/0.54    r1_tarski(k1_tarski(sK1),k1_tarski(sK2)) | k2_tarski(sK0,sK1) = k1_tarski(sK1) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 1.29/0.54    inference(superposition,[],[f35,f222])).
% 1.29/0.54  fof(f222,plain,(
% 1.29/0.54    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k2_tarski(sK0,sK1) = k1_tarski(sK1) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 1.29/0.54    inference(backward_demodulation,[],[f178,f210])).
% 1.29/0.54  fof(f178,plain,(
% 1.29/0.54    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3) | sK1 = sK2),
% 1.29/0.54    inference(subsumption_resolution,[],[f170,f20])).
% 1.29/0.54  fof(f170,plain,(
% 1.29/0.54    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3) | sK0 = sK2 | sK1 = sK2),
% 1.29/0.54    inference(resolution,[],[f73,f32])).
% 1.29/0.54  fof(f73,plain,(
% 1.29/0.54    r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 1.29/0.54    inference(superposition,[],[f36,f61])).
% 1.29/0.54  fof(f212,plain,(
% 1.29/0.54    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK1))),
% 1.29/0.54    inference(backward_demodulation,[],[f47,f210])).
% 1.29/0.54  fof(f47,plain,(
% 1.29/0.54    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.29/0.54    inference(resolution,[],[f25,f19])).
% 1.29/0.54  % SZS output end Proof for theBenchmark
% 1.29/0.54  % (7197)------------------------------
% 1.29/0.54  % (7197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (7197)Termination reason: Refutation
% 1.29/0.54  
% 1.29/0.54  % (7197)Memory used [KB]: 6396
% 1.29/0.54  % (7197)Time elapsed: 0.121 s
% 1.29/0.54  % (7197)------------------------------
% 1.29/0.54  % (7197)------------------------------
% 1.29/0.54  % (7216)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (7196)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.54  % (7211)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.46/0.54  % (7189)Success in time 0.178 s
%------------------------------------------------------------------------------
