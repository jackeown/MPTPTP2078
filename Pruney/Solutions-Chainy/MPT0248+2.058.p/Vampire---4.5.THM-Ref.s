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
% DateTime   : Thu Dec  3 12:37:57 EST 2020

% Result     : Theorem 2.02s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 765 expanded)
%              Number of leaves         :   18 ( 221 expanded)
%              Depth                    :   17
%              Number of atoms          :  169 (2407 expanded)
%              Number of equality atoms :   90 (1677 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2419,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2418,f2281])).

fof(f2281,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f2031,f2158])).

fof(f2158,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f2028,f2031])).

fof(f2028,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f2025,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2025,plain,
    ( v1_xboole_0(sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f2024,f117])).

fof(f117,plain,(
    sK1 = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f72,f88])).

fof(f88,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f61,f51])).

fof(f51,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f43])).

fof(f43,plain,
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

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f61,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2024,plain,
    ( v1_xboole_0(sK1)
    | k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f2022,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f2022,plain,
    ( r2_hidden(sK0,sK1)
    | v1_xboole_0(sK1) ),
    inference(superposition,[],[f2011,f117])).

fof(f2011,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1)))
      | r2_hidden(X1,X2) ) ),
    inference(superposition,[],[f2000,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2000,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k3_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f103,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_xboole_0(k1_tarski(X1),X2))
      | r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2031,plain,(
    sK1 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f54,f2030])).

fof(f2030,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f53,f52,f2028,f2029])).

fof(f2029,plain,
    ( sK2 = k1_tarski(sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f2027,f58])).

fof(f2027,plain,
    ( v1_xboole_0(sK2)
    | sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f2026,f544])).

fof(f544,plain,(
    sK2 = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f475,f72])).

fof(f475,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f233,f456])).

fof(f456,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f451,f56])).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f451,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f66,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f233,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(sK2,X7),k1_tarski(sK0)) ),
    inference(superposition,[],[f166,f51])).

fof(f166,plain,(
    ! [X8,X7,X9] : r1_tarski(k4_xboole_0(X7,X8),k2_xboole_0(X9,X7)) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f2026,plain,
    ( v1_xboole_0(sK2)
    | k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0)) ),
    inference(resolution,[],[f2023,f70])).

fof(f2023,plain,
    ( r2_hidden(sK0,sK2)
    | v1_xboole_0(sK2) ),
    inference(superposition,[],[f2011,f544])).

fof(f52,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f53,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f54,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f44])).

fof(f2418,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f2417,f464])).

fof(f464,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(superposition,[],[f107,f456])).

fof(f107,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(resolution,[],[f71,f62])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2417,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2032,f2158])).

fof(f2032,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f51,f2030])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:44:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (21601)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.50  % (21593)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.50  % (21604)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.50  % (21586)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (21585)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (21582)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (21601)Refutation not found, incomplete strategy% (21601)------------------------------
% 0.21/0.51  % (21601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21601)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21601)Memory used [KB]: 10746
% 0.21/0.51  % (21601)Time elapsed: 0.057 s
% 0.21/0.51  % (21601)------------------------------
% 0.21/0.51  % (21601)------------------------------
% 0.21/0.51  % (21589)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (21590)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (21588)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (21596)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (21602)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (21598)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (21579)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (21594)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (21594)Refutation not found, incomplete strategy% (21594)------------------------------
% 0.21/0.53  % (21594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21594)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21594)Memory used [KB]: 6140
% 0.21/0.53  % (21594)Time elapsed: 0.002 s
% 0.21/0.53  % (21594)------------------------------
% 0.21/0.53  % (21594)------------------------------
% 0.21/0.53  % (21583)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21581)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (21596)Refutation not found, incomplete strategy% (21596)------------------------------
% 0.21/0.53  % (21596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21596)Memory used [KB]: 10618
% 0.21/0.53  % (21596)Time elapsed: 0.111 s
% 0.21/0.53  % (21596)------------------------------
% 0.21/0.53  % (21596)------------------------------
% 0.21/0.53  % (21605)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (21591)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (21580)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (21584)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (21608)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (21603)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21607)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (21600)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (21597)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (21606)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21599)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (21595)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (21587)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (21592)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.02/0.62  % (21586)Refutation found. Thanks to Tanya!
% 2.02/0.62  % SZS status Theorem for theBenchmark
% 2.02/0.62  % SZS output start Proof for theBenchmark
% 2.02/0.62  fof(f2419,plain,(
% 2.02/0.62    $false),
% 2.02/0.62    inference(subsumption_resolution,[],[f2418,f2281])).
% 2.02/0.62  fof(f2281,plain,(
% 2.02/0.62    k1_xboole_0 != k1_tarski(sK0)),
% 2.02/0.62    inference(backward_demodulation,[],[f2031,f2158])).
% 2.02/0.62  fof(f2158,plain,(
% 2.02/0.62    k1_xboole_0 = sK1),
% 2.02/0.62    inference(subsumption_resolution,[],[f2028,f2031])).
% 2.02/0.62  fof(f2028,plain,(
% 2.02/0.62    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 2.02/0.62    inference(resolution,[],[f2025,f58])).
% 2.02/0.62  fof(f58,plain,(
% 2.02/0.62    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 2.02/0.62    inference(cnf_transformation,[],[f32])).
% 2.02/0.62  fof(f32,plain,(
% 2.02/0.62    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.02/0.62    inference(ennf_transformation,[],[f3])).
% 2.02/0.62  fof(f3,axiom,(
% 2.02/0.62    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.02/0.62  fof(f2025,plain,(
% 2.02/0.62    v1_xboole_0(sK1) | sK1 = k1_tarski(sK0)),
% 2.02/0.62    inference(forward_demodulation,[],[f2024,f117])).
% 2.02/0.62  fof(f117,plain,(
% 2.02/0.62    sK1 = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.02/0.62    inference(resolution,[],[f72,f88])).
% 2.02/0.62  fof(f88,plain,(
% 2.02/0.62    r1_tarski(sK1,k1_tarski(sK0))),
% 2.02/0.62    inference(superposition,[],[f61,f51])).
% 2.02/0.62  fof(f51,plain,(
% 2.02/0.62    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.02/0.62    inference(cnf_transformation,[],[f44])).
% 2.02/0.62  fof(f44,plain,(
% 2.02/0.62    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.02/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f43])).
% 2.02/0.62  fof(f43,plain,(
% 2.02/0.62    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 2.02/0.62    introduced(choice_axiom,[])).
% 2.02/0.62  fof(f31,plain,(
% 2.02/0.62    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.02/0.62    inference(ennf_transformation,[],[f28])).
% 2.02/0.62  fof(f28,negated_conjecture,(
% 2.02/0.62    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.02/0.62    inference(negated_conjecture,[],[f27])).
% 2.02/0.62  fof(f27,conjecture,(
% 2.02/0.62    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.02/0.62  fof(f61,plain,(
% 2.02/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.02/0.62    inference(cnf_transformation,[],[f16])).
% 2.02/0.62  fof(f16,axiom,(
% 2.02/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.02/0.62  fof(f72,plain,(
% 2.02/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.02/0.62    inference(cnf_transformation,[],[f39])).
% 2.02/0.62  fof(f39,plain,(
% 2.02/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.02/0.62    inference(ennf_transformation,[],[f11])).
% 2.02/0.62  fof(f11,axiom,(
% 2.02/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.02/0.62  fof(f2024,plain,(
% 2.02/0.62    v1_xboole_0(sK1) | k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.02/0.62    inference(resolution,[],[f2022,f70])).
% 2.02/0.62  fof(f70,plain,(
% 2.02/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 2.02/0.62    inference(cnf_transformation,[],[f37])).
% 2.02/0.62  fof(f37,plain,(
% 2.02/0.62    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 2.02/0.62    inference(ennf_transformation,[],[f25])).
% 2.02/0.62  fof(f25,axiom,(
% 2.02/0.62    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 2.02/0.62  fof(f2022,plain,(
% 2.02/0.62    r2_hidden(sK0,sK1) | v1_xboole_0(sK1)),
% 2.02/0.62    inference(superposition,[],[f2011,f117])).
% 2.02/0.62  fof(f2011,plain,(
% 2.02/0.62    ( ! [X2,X1] : (v1_xboole_0(k3_xboole_0(X2,k1_tarski(X1))) | r2_hidden(X1,X2)) )),
% 2.02/0.62    inference(superposition,[],[f2000,f63])).
% 2.02/0.62  fof(f63,plain,(
% 2.02/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f1])).
% 2.02/0.62  fof(f1,axiom,(
% 2.02/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.02/0.62  fof(f2000,plain,(
% 2.02/0.62    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(k1_tarski(X0),X1)) | r2_hidden(X0,X1)) )),
% 2.02/0.62    inference(resolution,[],[f103,f60])).
% 2.02/0.62  fof(f60,plain,(
% 2.02/0.62    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f46])).
% 2.02/0.62  fof(f46,plain,(
% 2.02/0.62    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0))),
% 2.02/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f45])).
% 2.02/0.62  fof(f45,plain,(
% 2.02/0.62    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 2.02/0.62    introduced(choice_axiom,[])).
% 2.02/0.62  fof(f34,plain,(
% 2.02/0.62    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 2.02/0.62    inference(ennf_transformation,[],[f30])).
% 2.02/0.62  fof(f30,plain,(
% 2.02/0.62    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 2.02/0.62    inference(unused_predicate_definition_removal,[],[f2])).
% 2.02/0.62  fof(f2,axiom,(
% 2.02/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.02/0.62  fof(f103,plain,(
% 2.02/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_xboole_0(k1_tarski(X1),X2)) | r2_hidden(X1,X2)) )),
% 2.02/0.62    inference(resolution,[],[f68,f69])).
% 2.02/0.62  fof(f69,plain,(
% 2.02/0.62    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f36])).
% 2.02/0.62  fof(f36,plain,(
% 2.02/0.62    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.02/0.62    inference(ennf_transformation,[],[f24])).
% 2.02/0.62  fof(f24,axiom,(
% 2.02/0.62    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.02/0.62  fof(f68,plain,(
% 2.02/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.02/0.62    inference(cnf_transformation,[],[f48])).
% 2.02/0.62  fof(f48,plain,(
% 2.02/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f47])).
% 2.02/0.62  fof(f47,plain,(
% 2.02/0.62    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)))),
% 2.02/0.62    introduced(choice_axiom,[])).
% 2.02/0.62  fof(f35,plain,(
% 2.02/0.62    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.02/0.62    inference(ennf_transformation,[],[f29])).
% 2.02/0.62  fof(f29,plain,(
% 2.02/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.62    inference(rectify,[],[f5])).
% 2.02/0.62  fof(f5,axiom,(
% 2.02/0.62    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.02/0.62  fof(f2031,plain,(
% 2.02/0.62    sK1 != k1_tarski(sK0)),
% 2.02/0.62    inference(subsumption_resolution,[],[f54,f2030])).
% 2.02/0.62  fof(f2030,plain,(
% 2.02/0.62    k1_xboole_0 = sK2),
% 2.02/0.62    inference(global_subsumption,[],[f53,f52,f2028,f2029])).
% 2.02/0.62  fof(f2029,plain,(
% 2.02/0.62    sK2 = k1_tarski(sK0) | k1_xboole_0 = sK2),
% 2.02/0.62    inference(resolution,[],[f2027,f58])).
% 2.02/0.62  fof(f2027,plain,(
% 2.02/0.62    v1_xboole_0(sK2) | sK2 = k1_tarski(sK0)),
% 2.02/0.62    inference(forward_demodulation,[],[f2026,f544])).
% 2.02/0.62  fof(f544,plain,(
% 2.02/0.62    sK2 = k3_xboole_0(sK2,k1_tarski(sK0))),
% 2.02/0.62    inference(resolution,[],[f475,f72])).
% 2.02/0.62  fof(f475,plain,(
% 2.02/0.62    r1_tarski(sK2,k1_tarski(sK0))),
% 2.02/0.62    inference(superposition,[],[f233,f456])).
% 2.02/0.62  fof(f456,plain,(
% 2.02/0.62    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 2.02/0.62    inference(forward_demodulation,[],[f451,f56])).
% 2.02/0.62  fof(f56,plain,(
% 2.02/0.62    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.02/0.62    inference(cnf_transformation,[],[f15])).
% 2.02/0.62  fof(f15,axiom,(
% 2.02/0.62    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.02/0.62  fof(f451,plain,(
% 2.02/0.62    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 2.02/0.62    inference(superposition,[],[f66,f55])).
% 2.02/0.62  fof(f55,plain,(
% 2.02/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f12])).
% 2.02/0.62  fof(f12,axiom,(
% 2.02/0.62    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.02/0.62  fof(f66,plain,(
% 2.02/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.02/0.62    inference(cnf_transformation,[],[f7])).
% 2.02/0.62  fof(f7,axiom,(
% 2.02/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.02/0.62  fof(f233,plain,(
% 2.02/0.62    ( ! [X7] : (r1_tarski(k4_xboole_0(sK2,X7),k1_tarski(sK0))) )),
% 2.02/0.62    inference(superposition,[],[f166,f51])).
% 2.02/0.62  fof(f166,plain,(
% 2.02/0.62    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(X7,X8),k2_xboole_0(X9,X7))) )),
% 2.02/0.62    inference(resolution,[],[f76,f62])).
% 2.02/0.62  fof(f62,plain,(
% 2.02/0.62    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.02/0.62    inference(cnf_transformation,[],[f13])).
% 2.02/0.62  fof(f13,axiom,(
% 2.02/0.62    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.02/0.62  fof(f76,plain,(
% 2.02/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 2.02/0.62    inference(cnf_transformation,[],[f40])).
% 2.02/0.62  fof(f40,plain,(
% 2.02/0.62    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.02/0.62    inference(ennf_transformation,[],[f9])).
% 2.02/0.62  fof(f9,axiom,(
% 2.02/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 2.02/0.62  fof(f2026,plain,(
% 2.02/0.62    v1_xboole_0(sK2) | k1_tarski(sK0) = k3_xboole_0(sK2,k1_tarski(sK0))),
% 2.02/0.62    inference(resolution,[],[f2023,f70])).
% 2.02/0.62  fof(f2023,plain,(
% 2.02/0.62    r2_hidden(sK0,sK2) | v1_xboole_0(sK2)),
% 2.02/0.62    inference(superposition,[],[f2011,f544])).
% 2.02/0.62  fof(f52,plain,(
% 2.02/0.62    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 2.02/0.62    inference(cnf_transformation,[],[f44])).
% 2.02/0.62  fof(f53,plain,(
% 2.02/0.62    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 2.02/0.62    inference(cnf_transformation,[],[f44])).
% 2.02/0.62  fof(f54,plain,(
% 2.02/0.62    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.02/0.62    inference(cnf_transformation,[],[f44])).
% 2.02/0.62  fof(f2418,plain,(
% 2.02/0.62    k1_xboole_0 = k1_tarski(sK0)),
% 2.02/0.62    inference(forward_demodulation,[],[f2417,f464])).
% 2.02/0.62  fof(f464,plain,(
% 2.02/0.62    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 2.02/0.62    inference(superposition,[],[f107,f456])).
% 2.02/0.62  fof(f107,plain,(
% 2.02/0.62    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 2.02/0.62    inference(resolution,[],[f71,f62])).
% 2.02/0.62  fof(f71,plain,(
% 2.02/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.02/0.62    inference(cnf_transformation,[],[f38])).
% 2.02/0.62  fof(f38,plain,(
% 2.02/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.02/0.62    inference(ennf_transformation,[],[f10])).
% 2.02/0.62  fof(f10,axiom,(
% 2.02/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.02/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.02/0.62  fof(f2417,plain,(
% 2.02/0.62    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.02/0.62    inference(forward_demodulation,[],[f2032,f2158])).
% 2.02/0.62  fof(f2032,plain,(
% 2.02/0.62    k1_tarski(sK0) = k2_xboole_0(sK1,k1_xboole_0)),
% 2.02/0.62    inference(backward_demodulation,[],[f51,f2030])).
% 2.02/0.62  % SZS output end Proof for theBenchmark
% 2.02/0.62  % (21586)------------------------------
% 2.02/0.62  % (21586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.62  % (21586)Termination reason: Refutation
% 2.02/0.62  
% 2.02/0.62  % (21586)Memory used [KB]: 7931
% 2.02/0.62  % (21586)Time elapsed: 0.211 s
% 2.02/0.62  % (21586)------------------------------
% 2.02/0.62  % (21586)------------------------------
% 2.08/0.63  % (21578)Success in time 0.269 s
%------------------------------------------------------------------------------
