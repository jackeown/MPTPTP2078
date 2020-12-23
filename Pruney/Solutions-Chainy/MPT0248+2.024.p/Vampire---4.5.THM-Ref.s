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
% DateTime   : Thu Dec  3 12:37:52 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :   75 (1452 expanded)
%              Number of leaves         :   11 ( 464 expanded)
%              Depth                    :   21
%              Number of atoms          :  177 (2992 expanded)
%              Number of equality atoms :  147 (2771 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f248])).

fof(f248,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f245,f247])).

fof(f247,plain,(
    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f246,f66])).

fof(f66,plain,(
    ! [X0] : k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f30,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f246,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f233,f240])).

fof(f240,plain,(
    k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f239])).

fof(f239,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f155,f227])).

fof(f227,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f101,f202])).

fof(f202,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f201])).

fof(f201,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f100,f138])).

% (7682)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (7695)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f138,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f85,f84])).

fof(f84,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f46,f56])).

fof(f56,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f49,f43])).

fof(f43,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f20,f39,f38])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f24,f39,f39])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f85,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f77,f46])).

fof(f77,plain,(
    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f71,f43])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0))) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f31,f38,f38])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f100,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f91])).

fof(f91,plain,
    ( sK1 != sK1
    | sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f55,f84])).

fof(f55,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f54])).

fof(f54,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f42])).

fof(f42,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f21,f39,f39])).

fof(f21,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f40,f84])).

fof(f40,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f23,f39])).

fof(f23,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f155,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,
    ( sK2 != sK2
    | k1_xboole_0 != sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f41,f85])).

fof(f41,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f22,f39])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f233,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f43,f227])).

fof(f245,plain,(
    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f241,f240])).

fof(f241,plain,(
    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(trivial_inequality_removal,[],[f232])).

fof(f232,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(backward_demodulation,[],[f41,f227])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:27:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.55  % (7680)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (7699)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (7691)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.43/0.56  % (7680)Refutation found. Thanks to Tanya!
% 1.43/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.57  % (7703)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f258,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f248])).
% 1.43/0.57  fof(f248,plain,(
% 1.43/0.57    k1_xboole_0 != k1_xboole_0),
% 1.43/0.57    inference(superposition,[],[f245,f247])).
% 1.43/0.57  fof(f247,plain,(
% 1.43/0.57    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.43/0.57    inference(forward_demodulation,[],[f246,f66])).
% 1.43/0.57  fof(f66,plain,(
% 1.43/0.57    ( ! [X0] : (k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0) )),
% 1.43/0.57    inference(resolution,[],[f47,f52])).
% 1.43/0.57  fof(f52,plain,(
% 1.43/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.43/0.57    inference(equality_resolution,[],[f28])).
% 1.43/0.57  fof(f28,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.43/0.57    inference(cnf_transformation,[],[f19])).
% 1.43/0.57  fof(f19,plain,(
% 1.43/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.57    inference(flattening,[],[f18])).
% 1.43/0.57  fof(f18,plain,(
% 1.43/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.43/0.57    inference(nnf_transformation,[],[f2])).
% 1.43/0.57  fof(f2,axiom,(
% 1.43/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.43/0.57  fof(f47,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1) )),
% 1.43/0.57    inference(definition_unfolding,[],[f30,f38])).
% 1.43/0.57  fof(f38,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f35,f37])).
% 1.43/0.57  fof(f37,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f34,f36])).
% 1.43/0.57  fof(f36,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f7])).
% 1.43/0.57  fof(f7,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.43/0.57  fof(f34,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f6])).
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.43/0.57  fof(f35,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f9])).
% 1.43/0.57  fof(f9,axiom,(
% 1.43/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f13])).
% 1.43/0.57  fof(f13,plain,(
% 1.43/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f3])).
% 1.43/0.57  fof(f3,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.43/0.57  fof(f246,plain,(
% 1.43/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))),
% 1.43/0.57    inference(forward_demodulation,[],[f233,f240])).
% 1.43/0.57  fof(f240,plain,(
% 1.43/0.57    k1_xboole_0 = sK2),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f239])).
% 1.43/0.57  fof(f239,plain,(
% 1.43/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2),
% 1.43/0.57    inference(backward_demodulation,[],[f155,f227])).
% 1.43/0.57  fof(f227,plain,(
% 1.43/0.57    k1_xboole_0 = sK1),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f226])).
% 1.43/0.57  fof(f226,plain,(
% 1.43/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(duplicate_literal_removal,[],[f218])).
% 1.43/0.57  fof(f218,plain,(
% 1.43/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(superposition,[],[f101,f202])).
% 1.43/0.57  fof(f202,plain,(
% 1.43/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f201])).
% 1.43/0.57  fof(f201,plain,(
% 1.43/0.57    sK1 != sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.43/0.57    inference(duplicate_literal_removal,[],[f188])).
% 1.43/0.57  fof(f188,plain,(
% 1.43/0.57    sK1 != sK1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(superposition,[],[f100,f138])).
% 1.43/0.57  % (7682)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.43/0.57  % (7695)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.57  fof(f138,plain,(
% 1.43/0.57    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(superposition,[],[f85,f84])).
% 1.43/0.57  fof(f84,plain,(
% 1.43/0.57    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 1.43/0.57    inference(resolution,[],[f46,f56])).
% 1.43/0.57  fof(f56,plain,(
% 1.43/0.57    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.43/0.57    inference(superposition,[],[f49,f43])).
% 1.43/0.57  fof(f43,plain,(
% 1.43/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.43/0.57    inference(definition_unfolding,[],[f20,f39,f38])).
% 1.43/0.57  fof(f39,plain,(
% 1.43/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.43/0.57    inference(definition_unfolding,[],[f32,f37])).
% 1.43/0.57  fof(f32,plain,(
% 1.43/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f5])).
% 1.43/0.57  fof(f5,axiom,(
% 1.43/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.43/0.57  fof(f20,plain,(
% 1.43/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f15,plain,(
% 1.43/0.57    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 1.43/0.57  fof(f14,plain,(
% 1.43/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f12,plain,(
% 1.43/0.57    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.43/0.57    inference(ennf_transformation,[],[f11])).
% 1.43/0.57  fof(f11,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.43/0.57    inference(negated_conjecture,[],[f10])).
% 1.43/0.57  fof(f10,conjecture,(
% 1.43/0.57    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.43/0.57  fof(f49,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f33,f38])).
% 1.43/0.57  fof(f33,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.43/0.57  fof(f46,plain,(
% 1.43/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.43/0.57    inference(definition_unfolding,[],[f24,f39,f39])).
% 1.43/0.57  fof(f24,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f17])).
% 1.43/0.57  fof(f17,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.43/0.57    inference(flattening,[],[f16])).
% 1.43/0.57  fof(f16,plain,(
% 1.43/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.43/0.57    inference(nnf_transformation,[],[f8])).
% 1.43/0.57  fof(f8,axiom,(
% 1.43/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.43/0.57  fof(f85,plain,(
% 1.43/0.57    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 1.43/0.57    inference(resolution,[],[f77,f46])).
% 1.43/0.57  fof(f77,plain,(
% 1.43/0.57    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.43/0.57    inference(superposition,[],[f71,f43])).
% 1.43/0.57  fof(f71,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X1,X1,X1,X0)))) )),
% 1.43/0.57    inference(superposition,[],[f49,f48])).
% 1.43/0.57  fof(f48,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 1.43/0.57    inference(definition_unfolding,[],[f31,f38,f38])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f1])).
% 1.43/0.57  fof(f1,axiom,(
% 1.43/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.43/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.43/0.57  fof(f100,plain,(
% 1.43/0.57    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f91])).
% 1.43/0.57  fof(f91,plain,(
% 1.43/0.57    sK1 != sK1 | sK1 != sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(superposition,[],[f55,f84])).
% 1.43/0.57  fof(f55,plain,(
% 1.43/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.43/0.57    inference(inner_rewriting,[],[f54])).
% 1.43/0.57  fof(f54,plain,(
% 1.43/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.43/0.57    inference(inner_rewriting,[],[f42])).
% 1.43/0.57  fof(f42,plain,(
% 1.43/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.43/0.57    inference(definition_unfolding,[],[f21,f39,f39])).
% 1.43/0.57  fof(f21,plain,(
% 1.43/0.57    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f101,plain,(
% 1.43/0.57    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f89])).
% 1.43/0.57  fof(f89,plain,(
% 1.43/0.57    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.43/0.57    inference(superposition,[],[f40,f84])).
% 1.43/0.57  fof(f40,plain,(
% 1.43/0.57    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.43/0.57    inference(definition_unfolding,[],[f23,f39])).
% 1.43/0.57  fof(f23,plain,(
% 1.43/0.57    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f155,plain,(
% 1.43/0.57    k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f140])).
% 1.43/0.57  fof(f140,plain,(
% 1.43/0.57    sK2 != sK2 | k1_xboole_0 != sK1 | k1_xboole_0 = sK2),
% 1.43/0.57    inference(superposition,[],[f41,f85])).
% 1.43/0.57  fof(f41,plain,(
% 1.43/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.43/0.57    inference(definition_unfolding,[],[f22,f39])).
% 1.43/0.57  fof(f22,plain,(
% 1.43/0.57    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.43/0.57    inference(cnf_transformation,[],[f15])).
% 1.43/0.57  fof(f233,plain,(
% 1.43/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 1.43/0.57    inference(backward_demodulation,[],[f43,f227])).
% 1.43/0.57  fof(f245,plain,(
% 1.43/0.57    k1_xboole_0 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.43/0.57    inference(forward_demodulation,[],[f241,f240])).
% 1.43/0.57  fof(f241,plain,(
% 1.43/0.57    sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.43/0.57    inference(trivial_inequality_removal,[],[f232])).
% 1.43/0.57  fof(f232,plain,(
% 1.43/0.57    k1_xboole_0 != k1_xboole_0 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.43/0.57    inference(backward_demodulation,[],[f41,f227])).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (7680)------------------------------
% 1.43/0.57  % (7680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (7680)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (7680)Memory used [KB]: 1791
% 1.43/0.57  % (7680)Time elapsed: 0.130 s
% 1.43/0.57  % (7680)------------------------------
% 1.43/0.57  % (7680)------------------------------
% 1.43/0.58  % (7674)Success in time 0.204 s
%------------------------------------------------------------------------------
