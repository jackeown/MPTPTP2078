%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 439 expanded)
%              Number of leaves         :   16 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  116 ( 523 expanded)
%              Number of equality atoms :   60 ( 431 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f56,f56,f691,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f92,f95])).

fof(f95,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f80,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f691,plain,(
    ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(trivial_inequality_removal,[],[f690])).

fof(f690,plain,
    ( sK3 != sK3
    | ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3) ),
    inference(superposition,[],[f190,f666])).

fof(f666,plain,(
    ! [X4,X3] :
      ( k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = X4
      | ~ r1_tarski(X3,X4) ) ),
    inference(forward_demodulation,[],[f659,f99])).

fof(f99,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f58,f96])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f95])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f659,plain,(
    ! [X4,X3] :
      ( k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k1_xboole_0))
      | ~ r1_tarski(X3,X4) ) ),
    inference(backward_demodulation,[],[f175,f653])).

fof(f653,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f609,f596])).

fof(f596,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f495,f208])).

fof(f208,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3 ),
    inference(forward_demodulation,[],[f202,f163])).

fof(f163,plain,(
    ! [X0] : k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f101,f99])).

fof(f101,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f61,f96,f96])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f202,plain,(
    ! [X3] : k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X3)) ),
    inference(superposition,[],[f163,f103])).

fof(f103,plain,(
    ! [X0,X1] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f66,f96,f96,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f495,plain,(
    ! [X14] : k5_xboole_0(X14,X14) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X14)) ),
    inference(subsumption_resolution,[],[f489,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f489,plain,(
    ! [X14] :
      ( k5_xboole_0(X14,X14) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X14))
      | ~ r1_tarski(X14,X14) ) ),
    inference(superposition,[],[f187,f163])).

fof(f187,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k5_xboole_0(k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)),k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)))
      | ~ r1_tarski(k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)),X4) ) ),
    inference(superposition,[],[f102,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f102,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1)) ),
    inference(definition_unfolding,[],[f65,f64,f64,f96])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f609,plain,(
    ! [X3] : k5_xboole_0(X3,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f595,f206])).

fof(f206,plain,(
    ! [X3] : r1_tarski(k1_xboole_0,X3) ),
    inference(superposition,[],[f100,f163])).

fof(f100,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f96])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f595,plain,(
    ! [X3] :
      ( k5_xboole_0(X3,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,X3) ) ),
    inference(superposition,[],[f495,f72])).

fof(f175,plain,(
    ! [X4,X3] :
      ( k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3)))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f103,f72])).

fof(f190,plain,(
    sK3 != k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2))) ),
    inference(superposition,[],[f98,f101])).

fof(f98,plain,(
    sK3 != k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)) ),
    inference(definition_unfolding,[],[f57,f96,f97])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f95])).

fof(f59,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f57,plain,(
    sK3 != k2_xboole_0(k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK3 != k2_xboole_0(k1_tarski(sK2),sK3)
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK3 != k2_xboole_0(k1_tarski(sK2),sK3)
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f56,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:53:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (26596)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.47  % (26604)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (26594)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (26592)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (26594)Refutation not found, incomplete strategy% (26594)------------------------------
% 0.20/0.51  % (26594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26594)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26594)Memory used [KB]: 10618
% 0.20/0.51  % (26594)Time elapsed: 0.117 s
% 0.20/0.51  % (26594)------------------------------
% 0.20/0.51  % (26594)------------------------------
% 0.20/0.51  % (26593)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (26593)Refutation not found, incomplete strategy% (26593)------------------------------
% 0.20/0.51  % (26593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26593)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26593)Memory used [KB]: 10618
% 0.20/0.51  % (26593)Time elapsed: 0.116 s
% 0.20/0.51  % (26593)------------------------------
% 0.20/0.51  % (26593)------------------------------
% 0.20/0.52  % (26588)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (26590)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (26607)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (26602)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (26583)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (26599)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (26584)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (26585)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (26586)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (26587)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (26605)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (26585)Refutation not found, incomplete strategy% (26585)------------------------------
% 0.20/0.53  % (26585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26585)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (26585)Memory used [KB]: 10746
% 0.20/0.53  % (26585)Time elapsed: 0.128 s
% 0.20/0.53  % (26585)------------------------------
% 0.20/0.53  % (26585)------------------------------
% 0.20/0.53  % (26597)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (26610)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (26611)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (26612)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (26598)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (26603)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (26601)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (26608)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (26600)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (26605)Refutation not found, incomplete strategy% (26605)------------------------------
% 0.20/0.54  % (26605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (26605)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (26605)Memory used [KB]: 10746
% 0.20/0.54  % (26605)Time elapsed: 0.102 s
% 0.20/0.54  % (26605)------------------------------
% 0.20/0.54  % (26605)------------------------------
% 0.20/0.54  % (26606)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (26609)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (26589)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (26591)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (26595)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.57  % (26591)Refutation not found, incomplete strategy% (26591)------------------------------
% 0.20/0.57  % (26591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (26591)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (26591)Memory used [KB]: 10746
% 0.20/0.57  % (26591)Time elapsed: 0.165 s
% 0.20/0.57  % (26591)------------------------------
% 0.20/0.57  % (26591)------------------------------
% 0.20/0.59  % (26612)Refutation found. Thanks to Tanya!
% 0.20/0.59  % SZS status Theorem for theBenchmark
% 0.20/0.59  % SZS output start Proof for theBenchmark
% 0.20/0.59  fof(f708,plain,(
% 0.20/0.59    $false),
% 0.20/0.59    inference(unit_resulting_resolution,[],[f56,f56,f691,f104])).
% 0.20/0.59  fof(f104,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f92,f95])).
% 0.20/0.59  fof(f95,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f63,f94])).
% 0.20/0.59  fof(f94,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f80,f93])).
% 0.20/0.59  fof(f93,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f18])).
% 0.20/0.59  fof(f18,axiom,(
% 0.20/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.59  fof(f80,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.59  fof(f63,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f16])).
% 0.20/0.59  fof(f16,axiom,(
% 0.20/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.59  fof(f92,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f55])).
% 0.20/0.59  fof(f55,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.59    inference(flattening,[],[f54])).
% 0.20/0.59  fof(f54,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.59    inference(nnf_transformation,[],[f20])).
% 0.20/0.59  fof(f20,axiom,(
% 0.20/0.59    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.59  fof(f691,plain,(
% 0.20/0.59    ~r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.20/0.59    inference(trivial_inequality_removal,[],[f690])).
% 0.20/0.59  fof(f690,plain,(
% 0.20/0.59    sK3 != sK3 | ~r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3)),
% 0.20/0.59    inference(superposition,[],[f190,f666])).
% 0.20/0.59  fof(f666,plain,(
% 0.20/0.59    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = X4 | ~r1_tarski(X3,X4)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f659,f99])).
% 0.20/0.59  fof(f99,plain,(
% 0.20/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.20/0.59    inference(definition_unfolding,[],[f58,f96])).
% 0.20/0.59  fof(f96,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f62,f95])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f19])).
% 0.20/0.59  fof(f19,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.59  fof(f58,plain,(
% 0.20/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.59    inference(cnf_transformation,[],[f10])).
% 0.20/0.59  fof(f10,axiom,(
% 0.20/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.59  fof(f659,plain,(
% 0.20/0.59    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k1_xboole_0)) | ~r1_tarski(X3,X4)) )),
% 0.20/0.59    inference(backward_demodulation,[],[f175,f653])).
% 0.20/0.59  fof(f653,plain,(
% 0.20/0.59    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 0.20/0.59    inference(forward_demodulation,[],[f609,f596])).
% 0.20/0.59  fof(f596,plain,(
% 0.20/0.59    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.59    inference(superposition,[],[f495,f208])).
% 0.20/0.59  fof(f208,plain,(
% 0.20/0.59    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = X3) )),
% 0.20/0.59    inference(forward_demodulation,[],[f202,f163])).
% 0.20/0.59  fof(f163,plain,(
% 0.20/0.59    ( ! [X0] : (k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 0.20/0.59    inference(superposition,[],[f101,f99])).
% 0.20/0.59  fof(f101,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f61,f96,f96])).
% 0.20/0.59  fof(f61,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f2])).
% 0.20/0.59  fof(f2,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.59  fof(f202,plain,(
% 0.20/0.59    ( ! [X3] : (k5_xboole_0(X3,k3_xboole_0(X3,k1_xboole_0)) = k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X3))) )),
% 0.20/0.59    inference(superposition,[],[f163,f103])).
% 0.20/0.59  fof(f103,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f66,f96,f96,f64])).
% 0.20/0.59  fof(f64,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f9])).
% 0.20/0.59  fof(f9,axiom,(
% 0.20/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.59  fof(f66,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f12])).
% 0.20/0.59  fof(f12,axiom,(
% 0.20/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.59  fof(f495,plain,(
% 0.20/0.59    ( ! [X14] : (k5_xboole_0(X14,X14) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X14))) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f489,f107])).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.59    inference(equality_resolution,[],[f75])).
% 0.20/0.59  fof(f75,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.59    inference(cnf_transformation,[],[f41])).
% 0.20/0.59  fof(f41,plain,(
% 0.20/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.59    inference(flattening,[],[f40])).
% 0.20/0.59  fof(f40,plain,(
% 0.20/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.59    inference(nnf_transformation,[],[f8])).
% 0.20/0.59  fof(f8,axiom,(
% 0.20/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.59  fof(f489,plain,(
% 0.20/0.59    ( ! [X14] : (k5_xboole_0(X14,X14) = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X14)) | ~r1_tarski(X14,X14)) )),
% 0.20/0.59    inference(superposition,[],[f187,f163])).
% 0.20/0.59  fof(f187,plain,(
% 0.20/0.59    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k5_xboole_0(k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)),k3_tarski(k3_enumset1(X3,X3,X3,X3,X4))) | ~r1_tarski(k3_tarski(k3_enumset1(X3,X3,X3,X3,X4)),X4)) )),
% 0.20/0.59    inference(superposition,[],[f102,f72])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f28])).
% 0.20/0.59  fof(f28,plain,(
% 0.20/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f11])).
% 0.20/0.59  fof(f11,axiom,(
% 0.20/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),k3_xboole_0(k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)),X1))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f65,f64,f64,f96])).
% 0.20/0.59  fof(f65,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f13])).
% 0.20/0.59  fof(f13,axiom,(
% 0.20/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.20/0.59  fof(f609,plain,(
% 0.20/0.59    ( ! [X3] : (k5_xboole_0(X3,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f595,f206])).
% 0.20/0.59  fof(f206,plain,(
% 0.20/0.59    ( ! [X3] : (r1_tarski(k1_xboole_0,X3)) )),
% 0.20/0.59    inference(superposition,[],[f100,f163])).
% 0.20/0.59  fof(f100,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 0.20/0.59    inference(definition_unfolding,[],[f60,f96])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.59    inference(cnf_transformation,[],[f14])).
% 0.20/0.59  fof(f14,axiom,(
% 0.20/0.59    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.59  fof(f595,plain,(
% 0.20/0.59    ( ! [X3] : (k5_xboole_0(X3,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,X3)) )),
% 0.20/0.59    inference(superposition,[],[f495,f72])).
% 0.20/0.59  fof(f175,plain,(
% 0.20/0.59    ( ! [X4,X3] : (k3_tarski(k3_enumset1(X4,X4,X4,X4,X3)) = k3_tarski(k3_enumset1(X4,X4,X4,X4,k5_xboole_0(X3,X3))) | ~r1_tarski(X3,X4)) )),
% 0.20/0.59    inference(superposition,[],[f103,f72])).
% 0.20/0.59  fof(f190,plain,(
% 0.20/0.59    sK3 != k3_tarski(k3_enumset1(sK3,sK3,sK3,sK3,k3_enumset1(sK2,sK2,sK2,sK2,sK2)))),
% 0.20/0.59    inference(superposition,[],[f98,f101])).
% 0.20/0.59  fof(f98,plain,(
% 0.20/0.59    sK3 != k3_tarski(k3_enumset1(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK2,sK2,sK2,sK2,sK2),sK3))),
% 0.20/0.59    inference(definition_unfolding,[],[f57,f96,f97])).
% 0.20/0.59  fof(f97,plain,(
% 0.20/0.59    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.20/0.59    inference(definition_unfolding,[],[f59,f95])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f15])).
% 0.20/0.59  fof(f15,axiom,(
% 0.20/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.59  fof(f57,plain,(
% 0.20/0.59    sK3 != k2_xboole_0(k1_tarski(sK2),sK3)),
% 0.20/0.59    inference(cnf_transformation,[],[f35])).
% 0.20/0.59  fof(f35,plain,(
% 0.20/0.59    sK3 != k2_xboole_0(k1_tarski(sK2),sK3) & r2_hidden(sK2,sK3)),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f25,f34])).
% 0.20/0.59  fof(f34,plain,(
% 0.20/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK3 != k2_xboole_0(k1_tarski(sK2),sK3) & r2_hidden(sK2,sK3))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f25,plain,(
% 0.20/0.59    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.20/0.59    inference(ennf_transformation,[],[f22])).
% 0.20/0.59  fof(f22,negated_conjecture,(
% 0.20/0.59    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.59    inference(negated_conjecture,[],[f21])).
% 0.20/0.59  fof(f21,conjecture,(
% 0.20/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.20/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.20/0.59  fof(f56,plain,(
% 0.20/0.59    r2_hidden(sK2,sK3)),
% 0.20/0.59    inference(cnf_transformation,[],[f35])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (26612)------------------------------
% 0.20/0.59  % (26612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (26612)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (26612)Memory used [KB]: 2174
% 0.20/0.59  % (26612)Time elapsed: 0.170 s
% 0.20/0.59  % (26612)------------------------------
% 0.20/0.59  % (26612)------------------------------
% 1.92/0.60  % (26582)Success in time 0.244 s
%------------------------------------------------------------------------------
