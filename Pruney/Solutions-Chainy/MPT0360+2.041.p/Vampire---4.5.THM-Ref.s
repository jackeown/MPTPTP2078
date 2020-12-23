%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:54 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 812 expanded)
%              Number of leaves         :    8 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :  148 (1193 expanded)
%              Number of equality atoms :   61 ( 762 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1099,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1098,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f1098,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f1097,f550])).

fof(f550,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f510,f549])).

fof(f549,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f548,f509])).

fof(f509,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f54,f501])).

fof(f501,plain,(
    ! [X22] : k1_xboole_0 = k3_xboole_0(X22,k1_xboole_0) ),
    inference(resolution,[],[f490,f145])).

fof(f145,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f144,f132])).

fof(f132,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f54,f123])).

fof(f123,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f115,f54])).

fof(f115,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f53,f54])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f29,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f144,plain,(
    ! [X3] : ~ r2_hidden(X3,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f139,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f69,f54])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f30])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f139,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(k1_xboole_0,k1_xboole_0))
      | r2_hidden(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f70,f123])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f30])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f490,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k3_xboole_0(X0,k1_xboole_0) = X1 ) ),
    inference(forward_demodulation,[],[f489,f115])).

fof(f489,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 ) ),
    inference(duplicate_literal_removal,[],[f451])).

fof(f451,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1
      | r2_hidden(sK4(X0,X0,X1),X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f49,f30])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f48,f30])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f548,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f511,f501])).

fof(f511,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f124,f501])).

fof(f124,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) ),
    inference(superposition,[],[f53,f115])).

fof(f510,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(backward_demodulation,[],[f115,f501])).

fof(f1097,plain,(
    sK1 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f1089,f549])).

fof(f1089,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1)) ),
    inference(resolution,[],[f1025,f25])).

fof(f25,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f1025,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | k5_xboole_0(X0,k3_xboole_0(X0,sK1)) = X0 ) ),
    inference(resolution,[],[f997,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f40,f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f997,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK1)
      | ~ r1_tarski(X3,sK2) ) ),
    inference(superposition,[],[f58,f988])).

fof(f988,plain,(
    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
    inference(duplicate_literal_removal,[],[f969])).

fof(f969,plain,
    ( sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))
    | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f818,f814])).

fof(f814,plain,(
    ! [X29] :
      ( ~ r2_hidden(sK4(sK2,X29,sK2),sK1)
      | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,X29)) ) ),
    inference(resolution,[],[f487,f198])).

fof(f198,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f69,f183])).

fof(f183,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f182,f56])).

fof(f182,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f179,f26])).

fof(f26,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f179,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k3_subset_1(sK0,sK2))
      | r1_xboole_0(X3,sK2) ) ),
    inference(superposition,[],[f58,f174])).

fof(f174,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f55,f24])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f487,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(factoring,[],[f64])).

fof(f818,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(X1,X2,X1),X2)
      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ) ),
    inference(subsumption_resolution,[],[f816,f64])).

fof(f816,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
      | r2_hidden(sK4(X1,X2,X1),X2)
      | ~ r2_hidden(sK4(X1,X2,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f800])).

fof(f800,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
      | r2_hidden(sK4(X1,X2,X1),X2)
      | ~ r2_hidden(sK4(X1,X2,X1),X1)
      | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ) ),
    inference(resolution,[],[f487,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f47,f30])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

% (15592)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
      | r1_xboole_0(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.58  % (15581)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.59  % (15598)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.59  % (15590)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.60  % (15597)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.60  % (15589)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (15597)Refutation not found, incomplete strategy% (15597)------------------------------
% 0.21/0.60  % (15597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (15582)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.61  % (15580)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.62  % (15597)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.62  
% 0.21/0.62  % (15597)Memory used [KB]: 10746
% 0.21/0.62  % (15597)Time elapsed: 0.159 s
% 0.21/0.62  % (15597)------------------------------
% 0.21/0.62  % (15597)------------------------------
% 1.86/0.62  % (15577)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.86/0.63  % (15578)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.86/0.63  % (15604)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.86/0.63  % (15579)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.86/0.63  % (15583)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.86/0.64  % (15576)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 2.12/0.64  % (15603)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 2.12/0.64  % (15596)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 2.12/0.64  % (15593)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 2.12/0.65  % (15575)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 2.12/0.65  % (15588)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.12/0.65  % (15595)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.12/0.65  % (15575)Refutation not found, incomplete strategy% (15575)------------------------------
% 2.12/0.65  % (15575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.65  % (15591)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.21/0.66  % (15601)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.21/0.66  % (15602)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.21/0.66  % (15594)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 2.21/0.66  % (15575)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.66  
% 2.21/0.66  % (15575)Memory used [KB]: 1663
% 2.21/0.66  % (15575)Time elapsed: 0.211 s
% 2.21/0.66  % (15575)------------------------------
% 2.21/0.66  % (15575)------------------------------
% 2.21/0.66  % (15586)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 2.21/0.66  % (15599)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.21/0.66  % (15587)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.21/0.66  % (15585)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 2.21/0.66  % (15585)Refutation not found, incomplete strategy% (15585)------------------------------
% 2.21/0.66  % (15585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.66  % (15585)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.66  
% 2.21/0.66  % (15585)Memory used [KB]: 10618
% 2.21/0.66  % (15585)Time elapsed: 0.231 s
% 2.21/0.66  % (15585)------------------------------
% 2.21/0.66  % (15585)------------------------------
% 2.21/0.67  % (15581)Refutation found. Thanks to Tanya!
% 2.21/0.67  % SZS status Theorem for theBenchmark
% 2.21/0.67  % SZS output start Proof for theBenchmark
% 2.21/0.67  fof(f1099,plain,(
% 2.21/0.67    $false),
% 2.21/0.67    inference(subsumption_resolution,[],[f1098,f27])).
% 2.21/0.67  fof(f27,plain,(
% 2.21/0.67    k1_xboole_0 != sK1),
% 2.21/0.67    inference(cnf_transformation,[],[f16])).
% 2.21/0.67  fof(f16,plain,(
% 2.21/0.67    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(flattening,[],[f15])).
% 2.21/0.67  fof(f15,plain,(
% 2.21/0.67    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f14])).
% 2.21/0.67  fof(f14,negated_conjecture,(
% 2.21/0.67    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.21/0.67    inference(negated_conjecture,[],[f13])).
% 2.21/0.67  fof(f13,conjecture,(
% 2.21/0.67    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 2.21/0.67  fof(f1098,plain,(
% 2.21/0.67    k1_xboole_0 = sK1),
% 2.21/0.67    inference(forward_demodulation,[],[f1097,f550])).
% 2.21/0.67  fof(f550,plain,(
% 2.21/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.21/0.67    inference(backward_demodulation,[],[f510,f549])).
% 2.21/0.67  fof(f549,plain,(
% 2.21/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.21/0.67    inference(forward_demodulation,[],[f548,f509])).
% 2.21/0.67  fof(f509,plain,(
% 2.21/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.67    inference(backward_demodulation,[],[f54,f501])).
% 2.21/0.67  fof(f501,plain,(
% 2.21/0.67    ( ! [X22] : (k1_xboole_0 = k3_xboole_0(X22,k1_xboole_0)) )),
% 2.21/0.67    inference(resolution,[],[f490,f145])).
% 2.21/0.67  fof(f145,plain,(
% 2.21/0.67    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 2.21/0.67    inference(forward_demodulation,[],[f144,f132])).
% 2.21/0.67  fof(f132,plain,(
% 2.21/0.67    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.21/0.67    inference(superposition,[],[f54,f123])).
% 2.21/0.67  fof(f123,plain,(
% 2.21/0.67    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.21/0.67    inference(superposition,[],[f115,f54])).
% 2.21/0.67  fof(f115,plain,(
% 2.21/0.67    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.21/0.67    inference(superposition,[],[f53,f54])).
% 2.21/0.67  fof(f53,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 2.21/0.67    inference(definition_unfolding,[],[f29,f30,f30])).
% 2.21/0.67  fof(f30,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f2])).
% 2.21/0.67  fof(f2,axiom,(
% 2.21/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.21/0.67  fof(f29,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.67    inference(cnf_transformation,[],[f5])).
% 2.21/0.67  fof(f5,axiom,(
% 2.21/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.21/0.67  fof(f144,plain,(
% 2.21/0.67    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f139,f97])).
% 2.21/0.67  fof(f97,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) )),
% 2.21/0.67    inference(superposition,[],[f69,f54])).
% 2.21/0.67  fof(f69,plain,(
% 2.21/0.67    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 2.21/0.67    inference(equality_resolution,[],[f61])).
% 2.21/0.67  fof(f61,plain,(
% 2.21/0.67    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.21/0.67    inference(definition_unfolding,[],[f51,f30])).
% 2.21/0.67  fof(f51,plain,(
% 2.21/0.67    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.21/0.67    inference(cnf_transformation,[],[f1])).
% 2.21/0.67  fof(f1,axiom,(
% 2.21/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.21/0.67  fof(f139,plain,(
% 2.21/0.67    ( ! [X3] : (~r2_hidden(X3,k5_xboole_0(k1_xboole_0,k1_xboole_0)) | r2_hidden(X3,k1_xboole_0)) )),
% 2.21/0.67    inference(superposition,[],[f70,f123])).
% 2.21/0.67  fof(f70,plain,(
% 2.21/0.67    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 2.21/0.67    inference(equality_resolution,[],[f62])).
% 2.21/0.67  fof(f62,plain,(
% 2.21/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.21/0.67    inference(definition_unfolding,[],[f50,f30])).
% 2.21/0.67  fof(f50,plain,(
% 2.21/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.21/0.67    inference(cnf_transformation,[],[f1])).
% 2.21/0.67  fof(f490,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k3_xboole_0(X0,k1_xboole_0) = X1) )),
% 2.21/0.67    inference(forward_demodulation,[],[f489,f115])).
% 2.21/0.67  fof(f489,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f451])).
% 2.21/0.67  fof(f451,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1 | r2_hidden(sK4(X0,X0,X1),X1) | k5_xboole_0(X0,k3_xboole_0(X0,X0)) = X1) )),
% 2.21/0.67    inference(resolution,[],[f64,f63])).
% 2.21/0.67  fof(f63,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.21/0.67    inference(definition_unfolding,[],[f49,f30])).
% 2.21/0.67  fof(f49,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.21/0.67    inference(cnf_transformation,[],[f1])).
% 2.21/0.67  fof(f64,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.21/0.67    inference(definition_unfolding,[],[f48,f30])).
% 2.21/0.67  fof(f48,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.21/0.67    inference(cnf_transformation,[],[f1])).
% 2.21/0.67  fof(f54,plain,(
% 2.21/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 2.21/0.67    inference(definition_unfolding,[],[f28,f30])).
% 2.21/0.67  fof(f28,plain,(
% 2.21/0.67    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.67    inference(cnf_transformation,[],[f4])).
% 2.21/0.67  fof(f4,axiom,(
% 2.21/0.67    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.21/0.67  fof(f548,plain,(
% 2.21/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.21/0.67    inference(forward_demodulation,[],[f511,f501])).
% 2.21/0.67  fof(f511,plain,(
% 2.21/0.67    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = k3_xboole_0(X0,X0)) )),
% 2.21/0.67    inference(backward_demodulation,[],[f124,f501])).
% 2.21/0.67  fof(f124,plain,(
% 2.21/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)))) )),
% 2.21/0.67    inference(superposition,[],[f53,f115])).
% 2.21/0.67  fof(f510,plain,(
% 2.21/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.21/0.67    inference(backward_demodulation,[],[f115,f501])).
% 2.21/0.67  fof(f1097,plain,(
% 2.21/0.67    sK1 = k5_xboole_0(sK1,sK1)),
% 2.21/0.67    inference(forward_demodulation,[],[f1089,f549])).
% 2.21/0.67  fof(f1089,plain,(
% 2.21/0.67    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK1))),
% 2.21/0.67    inference(resolution,[],[f1025,f25])).
% 2.21/0.67  fof(f25,plain,(
% 2.21/0.67    r1_tarski(sK1,sK2)),
% 2.21/0.67    inference(cnf_transformation,[],[f16])).
% 2.21/0.67  fof(f1025,plain,(
% 2.21/0.67    ( ! [X0] : (~r1_tarski(X0,sK2) | k5_xboole_0(X0,k3_xboole_0(X0,sK1)) = X0) )),
% 2.21/0.67    inference(resolution,[],[f997,f56])).
% 2.21/0.67  fof(f56,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.21/0.67    inference(definition_unfolding,[],[f40,f30])).
% 2.21/0.67  fof(f40,plain,(
% 2.21/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f7])).
% 2.21/0.67  fof(f7,axiom,(
% 2.21/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.21/0.67  fof(f997,plain,(
% 2.21/0.67    ( ! [X3] : (r1_xboole_0(X3,sK1) | ~r1_tarski(X3,sK2)) )),
% 2.21/0.67    inference(superposition,[],[f58,f988])).
% 2.21/0.67  fof(f988,plain,(
% 2.21/0.67    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f969])).
% 2.21/0.67  fof(f969,plain,(
% 2.21/0.67    sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,sK1))),
% 2.21/0.67    inference(resolution,[],[f818,f814])).
% 2.21/0.67  fof(f814,plain,(
% 2.21/0.67    ( ! [X29] : (~r2_hidden(sK4(sK2,X29,sK2),sK1) | sK2 = k5_xboole_0(sK2,k3_xboole_0(sK2,X29))) )),
% 2.21/0.67    inference(resolution,[],[f487,f198])).
% 2.21/0.67  fof(f198,plain,(
% 2.21/0.67    ( ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,sK1)) )),
% 2.21/0.67    inference(superposition,[],[f69,f183])).
% 2.21/0.67  fof(f183,plain,(
% 2.21/0.67    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 2.21/0.67    inference(resolution,[],[f182,f56])).
% 2.21/0.67  fof(f182,plain,(
% 2.21/0.67    r1_xboole_0(sK1,sK2)),
% 2.21/0.67    inference(resolution,[],[f179,f26])).
% 2.21/0.67  fof(f26,plain,(
% 2.21/0.67    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 2.21/0.67    inference(cnf_transformation,[],[f16])).
% 2.21/0.67  fof(f179,plain,(
% 2.21/0.67    ( ! [X3] : (~r1_tarski(X3,k3_subset_1(sK0,sK2)) | r1_xboole_0(X3,sK2)) )),
% 2.21/0.67    inference(superposition,[],[f58,f174])).
% 2.21/0.67  fof(f174,plain,(
% 2.21/0.67    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.21/0.67    inference(resolution,[],[f55,f24])).
% 2.21/0.67  fof(f24,plain,(
% 2.21/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.21/0.67    inference(cnf_transformation,[],[f16])).
% 2.21/0.67  fof(f55,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 2.21/0.67    inference(definition_unfolding,[],[f37,f30])).
% 2.21/0.67  fof(f37,plain,(
% 2.21/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f21])).
% 2.21/0.67  fof(f21,plain,(
% 2.21/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.21/0.67    inference(ennf_transformation,[],[f10])).
% 2.21/0.67  fof(f10,axiom,(
% 2.21/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.21/0.67  fof(f487,plain,(
% 2.21/0.67    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.21/0.67    inference(factoring,[],[f64])).
% 2.21/0.67  fof(f818,plain,(
% 2.21/0.67    ( ! [X2,X1] : (r2_hidden(sK4(X1,X2,X1),X2) | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1) )),
% 2.21/0.67    inference(subsumption_resolution,[],[f816,f64])).
% 2.21/0.67  fof(f816,plain,(
% 2.21/0.67    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1)) )),
% 2.21/0.67    inference(duplicate_literal_removal,[],[f800])).
% 2.21/0.67  fof(f800,plain,(
% 2.21/0.67    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1) | k5_xboole_0(X1,k3_xboole_0(X1,X2)) = X1) )),
% 2.21/0.67    inference(resolution,[],[f487,f65])).
% 2.21/0.67  fof(f65,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2) )),
% 2.21/0.67    inference(definition_unfolding,[],[f47,f30])).
% 2.21/0.67  fof(f47,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.21/0.67    inference(cnf_transformation,[],[f1])).
% 2.21/0.67  % (15592)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.21/0.67  fof(f58,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) | r1_xboole_0(X0,X2)) )),
% 2.21/0.67    inference(definition_unfolding,[],[f46,f30])).
% 2.21/0.67  fof(f46,plain,(
% 2.21/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.21/0.67    inference(cnf_transformation,[],[f23])).
% 2.21/0.67  fof(f23,plain,(
% 2.21/0.67    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.21/0.67    inference(ennf_transformation,[],[f3])).
% 2.21/0.67  fof(f3,axiom,(
% 2.21/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.21/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.21/0.67  % SZS output end Proof for theBenchmark
% 2.21/0.67  % (15581)------------------------------
% 2.21/0.67  % (15581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (15581)Termination reason: Refutation
% 2.21/0.67  
% 2.21/0.67  % (15581)Memory used [KB]: 7164
% 2.21/0.67  % (15581)Time elapsed: 0.228 s
% 2.21/0.67  % (15581)------------------------------
% 2.21/0.67  % (15581)------------------------------
% 2.21/0.67  % (15592)Refutation not found, incomplete strategy% (15592)------------------------------
% 2.21/0.67  % (15592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.67  % (15592)Termination reason: Refutation not found, incomplete strategy
% 2.21/0.67  
% 2.21/0.67  % (15592)Memory used [KB]: 10618
% 2.21/0.67  % (15592)Time elapsed: 0.228 s
% 2.21/0.67  % (15592)------------------------------
% 2.21/0.67  % (15592)------------------------------
% 2.21/0.68  % (15574)Success in time 0.308 s
%------------------------------------------------------------------------------
