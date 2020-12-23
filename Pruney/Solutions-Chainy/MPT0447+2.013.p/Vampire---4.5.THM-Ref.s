%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:10 EST 2020

% Result     : Theorem 4.64s
% Output     : Refutation 4.64s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 165 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  155 ( 538 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2776,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2775,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2775,plain,(
    ~ r1_tarski(k3_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f2766,f332])).

fof(f332,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f319,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f319,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f182,f65])).

fof(f65,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f39,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
          & r1_tarski(sK0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(X1))
        & r1_tarski(sK0,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f182,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X0)) ),
    inference(superposition,[],[f96,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f96,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1))) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f73,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f72,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f66,f39])).

fof(f66,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f2766,plain,(
    ~ r1_tarski(k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f2608,f350])).

fof(f350,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k4_xboole_0(k3_relat_1(sK0),X4),X5)
      | ~ r1_tarski(k2_xboole_0(X4,X5),k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f131,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f131,plain,(
    ! [X2] :
      ( ~ r1_tarski(k3_relat_1(sK0),X2)
      | ~ r1_tarski(X2,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f76,f46])).

fof(f76,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k3_relat_1(sK0),X0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f41,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f41,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f2608,plain,(
    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k3_relat_1(sK1)) ),
    inference(resolution,[],[f2397,f623])).

fof(f623,plain,(
    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f144,f55])).

fof(f144,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k3_relat_1(sK0))
      | r1_tarski(k4_xboole_0(X2,k1_relat_1(sK0)),k2_relat_1(sK0)) ) ),
    inference(superposition,[],[f50,f60])).

fof(f60,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f38,f42])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f2397,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k2_relat_1(sK0))
      | r1_tarski(X4,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f51,f1880])).

% (1172)Time limit reached!
% (1172)------------------------------
% (1172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f1880,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0)) ),
    inference(superposition,[],[f205,f47])).

fof(f205,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f199,f46])).

fof(f199,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f194,f39])).

fof(f194,plain,
    ( r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(superposition,[],[f102,f42])).

fof(f102,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1))) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f74,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f67,f39])).

fof(f67,plain,
    ( r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f40,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n025.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 09:33:50 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.43  % (1148)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.43  % (1167)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.43  % (1159)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.43  % (1165)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.44  % (1151)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.47  % (1157)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (1172)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (1147)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (1149)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (1173)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.53  % (1156)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.55  % (1146)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.55  % (1150)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.55  % (1171)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.55  % (1152)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.56  % (1145)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.56  % (1166)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.56  % (1158)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.56  % (1169)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.57  % (1170)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.57  % (1144)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.57  % (1164)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.58  % (1161)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.58  % (1162)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.58  % (1168)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.58  % (1163)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.59  % (1153)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.59  % (1154)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.59  % (1154)Refutation not found, incomplete strategy% (1154)------------------------------
% 0.19/0.59  % (1154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (1154)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.59  
% 0.19/0.59  % (1154)Memory used [KB]: 10618
% 0.19/0.59  % (1154)Time elapsed: 0.187 s
% 0.19/0.59  % (1154)------------------------------
% 0.19/0.59  % (1154)------------------------------
% 0.19/0.59  % (1160)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.59  % (1166)Refutation not found, incomplete strategy% (1166)------------------------------
% 0.19/0.59  % (1166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.59  % (1166)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.59  
% 0.19/0.59  % (1166)Memory used [KB]: 11001
% 0.19/0.59  % (1166)Time elapsed: 0.200 s
% 0.19/0.59  % (1166)------------------------------
% 0.19/0.59  % (1166)------------------------------
% 1.69/0.59  % (1155)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.69/0.59  % (1155)Refutation not found, incomplete strategy% (1155)------------------------------
% 1.69/0.59  % (1155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.59  % (1155)Termination reason: Refutation not found, incomplete strategy
% 1.69/0.59  
% 1.69/0.59  % (1155)Memory used [KB]: 10618
% 1.69/0.59  % (1155)Time elapsed: 0.196 s
% 1.69/0.59  % (1155)------------------------------
% 1.69/0.59  % (1155)------------------------------
% 2.57/0.73  % (1200)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.16/0.76  % (1201)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.16/0.77  % (1199)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.34/0.80  % (1149)Time limit reached!
% 3.34/0.80  % (1149)------------------------------
% 3.34/0.80  % (1149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.34/0.80  % (1149)Termination reason: Time limit
% 3.34/0.80  % (1149)Termination phase: Saturation
% 3.34/0.80  
% 3.34/0.80  % (1149)Memory used [KB]: 8443
% 3.34/0.80  % (1149)Time elapsed: 0.400 s
% 3.34/0.80  % (1149)------------------------------
% 3.34/0.80  % (1149)------------------------------
% 3.76/0.90  % (1144)Time limit reached!
% 3.76/0.90  % (1144)------------------------------
% 3.76/0.90  % (1144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.76/0.90  % (1144)Termination reason: Time limit
% 3.76/0.90  
% 3.76/0.90  % (1144)Memory used [KB]: 3709
% 3.76/0.90  % (1144)Time elapsed: 0.505 s
% 3.76/0.90  % (1144)------------------------------
% 3.76/0.90  % (1144)------------------------------
% 3.76/0.91  % (1161)Time limit reached!
% 3.76/0.91  % (1161)------------------------------
% 3.76/0.91  % (1161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.76/0.91  % (1161)Termination reason: Time limit
% 3.76/0.91  
% 3.76/0.91  % (1161)Memory used [KB]: 18677
% 3.76/0.91  % (1161)Time elapsed: 0.505 s
% 3.76/0.91  % (1161)------------------------------
% 3.76/0.91  % (1161)------------------------------
% 3.76/0.91  % (1145)Time limit reached!
% 3.76/0.91  % (1145)------------------------------
% 3.76/0.91  % (1145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.76/0.91  % (1145)Termination reason: Time limit
% 3.76/0.91  
% 3.76/0.91  % (1145)Memory used [KB]: 9083
% 3.76/0.91  % (1145)Time elapsed: 0.504 s
% 3.76/0.91  % (1145)------------------------------
% 3.76/0.91  % (1145)------------------------------
% 3.76/0.91  % (1268)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.30/0.92  % (1156)Time limit reached!
% 4.30/0.92  % (1156)------------------------------
% 4.30/0.92  % (1156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.30/0.93  % (1156)Termination reason: Time limit
% 4.30/0.93  
% 4.30/0.93  % (1156)Memory used [KB]: 9722
% 4.30/0.93  % (1156)Time elapsed: 0.517 s
% 4.30/0.93  % (1156)------------------------------
% 4.30/0.93  % (1156)------------------------------
% 4.64/0.99  % (1199)Refutation found. Thanks to Tanya!
% 4.64/0.99  % SZS status Theorem for theBenchmark
% 4.64/0.99  % SZS output start Proof for theBenchmark
% 4.64/0.99  fof(f2776,plain,(
% 4.64/0.99    $false),
% 4.64/0.99    inference(subsumption_resolution,[],[f2775,f55])).
% 4.64/0.99  fof(f55,plain,(
% 4.64/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.64/0.99    inference(equality_resolution,[],[f43])).
% 4.64/0.99  fof(f43,plain,(
% 4.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.64/0.99    inference(cnf_transformation,[],[f37])).
% 4.64/0.99  fof(f37,plain,(
% 4.64/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.64/0.99    inference(flattening,[],[f36])).
% 4.64/0.99  fof(f36,plain,(
% 4.64/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.64/0.99    inference(nnf_transformation,[],[f6])).
% 4.64/0.99  fof(f6,axiom,(
% 4.64/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.64/0.99  fof(f2775,plain,(
% 4.64/0.99    ~r1_tarski(k3_relat_1(sK1),k3_relat_1(sK1))),
% 4.64/0.99    inference(forward_demodulation,[],[f2766,f332])).
% 4.64/0.99  fof(f332,plain,(
% 4.64/0.99    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1))),
% 4.64/0.99    inference(resolution,[],[f319,f46])).
% 4.64/0.99  fof(f46,plain,(
% 4.64/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f26])).
% 4.64/0.99  fof(f26,plain,(
% 4.64/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.64/0.99    inference(ennf_transformation,[],[f9])).
% 4.64/0.99  fof(f9,axiom,(
% 4.64/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.64/0.99  fof(f319,plain,(
% 4.64/0.99    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 4.64/0.99    inference(superposition,[],[f182,f65])).
% 4.64/0.99  fof(f65,plain,(
% 4.64/0.99    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 4.64/0.99    inference(resolution,[],[f39,f42])).
% 4.64/0.99  fof(f42,plain,(
% 4.64/0.99    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f25])).
% 4.64/0.99  fof(f25,plain,(
% 4.64/0.99    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.64/0.99    inference(ennf_transformation,[],[f18])).
% 4.64/0.99  fof(f18,axiom,(
% 4.64/0.99    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 4.64/0.99  fof(f39,plain,(
% 4.64/0.99    v1_relat_1(sK1)),
% 4.64/0.99    inference(cnf_transformation,[],[f35])).
% 4.64/0.99  fof(f35,plain,(
% 4.64/0.99    (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 4.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f34,f33])).
% 4.64/0.99  fof(f33,plain,(
% 4.64/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 4.64/0.99    introduced(choice_axiom,[])).
% 4.64/0.99  fof(f34,plain,(
% 4.64/0.99    ? [X1] : (~r1_tarski(k3_relat_1(sK0),k3_relat_1(X1)) & r1_tarski(sK0,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK1))),
% 4.64/0.99    introduced(choice_axiom,[])).
% 4.64/0.99  fof(f24,plain,(
% 4.64/0.99    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 4.64/0.99    inference(flattening,[],[f23])).
% 4.64/0.99  fof(f23,plain,(
% 4.64/0.99    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 4.64/0.99    inference(ennf_transformation,[],[f22])).
% 4.64/0.99  fof(f22,negated_conjecture,(
% 4.64/0.99    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 4.64/0.99    inference(negated_conjecture,[],[f21])).
% 4.64/0.99  fof(f21,conjecture,(
% 4.64/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 4.64/0.99  fof(f182,plain,(
% 4.64/0.99    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(k1_relat_1(sK1),X0))) )),
% 4.64/0.99    inference(superposition,[],[f96,f47])).
% 4.64/0.99  fof(f47,plain,(
% 4.64/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f1])).
% 4.64/0.99  fof(f1,axiom,(
% 4.64/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 4.64/0.99  fof(f96,plain,(
% 4.64/0.99    ( ! [X0] : (r1_tarski(k1_relat_1(sK0),k2_xboole_0(X0,k1_relat_1(sK1)))) )),
% 4.64/0.99    inference(resolution,[],[f73,f51])).
% 4.64/0.99  fof(f51,plain,(
% 4.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f30])).
% 4.64/0.99  fof(f30,plain,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 4.64/0.99    inference(ennf_transformation,[],[f7])).
% 4.64/0.99  fof(f7,axiom,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 4.64/0.99  fof(f73,plain,(
% 4.64/0.99    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 4.64/0.99    inference(subsumption_resolution,[],[f72,f38])).
% 4.64/0.99  fof(f38,plain,(
% 4.64/0.99    v1_relat_1(sK0)),
% 4.64/0.99    inference(cnf_transformation,[],[f35])).
% 4.64/0.99  fof(f72,plain,(
% 4.64/0.99    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 4.64/0.99    inference(subsumption_resolution,[],[f66,f39])).
% 4.64/0.99  fof(f66,plain,(
% 4.64/0.99    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 4.64/0.99    inference(resolution,[],[f40,f52])).
% 4.64/0.99  fof(f52,plain,(
% 4.64/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f32])).
% 4.64/0.99  fof(f32,plain,(
% 4.64/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.64/0.99    inference(flattening,[],[f31])).
% 4.64/0.99  fof(f31,plain,(
% 4.64/0.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.64/0.99    inference(ennf_transformation,[],[f20])).
% 4.64/0.99  fof(f20,axiom,(
% 4.64/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 4.64/0.99  fof(f40,plain,(
% 4.64/0.99    r1_tarski(sK0,sK1)),
% 4.64/0.99    inference(cnf_transformation,[],[f35])).
% 4.64/0.99  fof(f2766,plain,(
% 4.64/0.99    ~r1_tarski(k2_xboole_0(k1_relat_1(sK0),k3_relat_1(sK1)),k3_relat_1(sK1))),
% 4.64/0.99    inference(resolution,[],[f2608,f350])).
% 4.64/0.99  fof(f350,plain,(
% 4.64/0.99    ( ! [X4,X5] : (~r1_tarski(k4_xboole_0(k3_relat_1(sK0),X4),X5) | ~r1_tarski(k2_xboole_0(X4,X5),k3_relat_1(sK1))) )),
% 4.64/0.99    inference(resolution,[],[f131,f49])).
% 4.64/0.99  fof(f49,plain,(
% 4.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f28])).
% 4.64/0.99  fof(f28,plain,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.64/0.99    inference(ennf_transformation,[],[f12])).
% 4.64/0.99  fof(f12,axiom,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 4.64/0.99  fof(f131,plain,(
% 4.64/0.99    ( ! [X2] : (~r1_tarski(k3_relat_1(sK0),X2) | ~r1_tarski(X2,k3_relat_1(sK1))) )),
% 4.64/0.99    inference(superposition,[],[f76,f46])).
% 4.64/0.99  fof(f76,plain,(
% 4.64/0.99    ( ! [X0] : (~r1_tarski(k2_xboole_0(k3_relat_1(sK0),X0),k3_relat_1(sK1))) )),
% 4.64/0.99    inference(resolution,[],[f41,f48])).
% 4.64/0.99  fof(f48,plain,(
% 4.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.64/0.99    inference(cnf_transformation,[],[f27])).
% 4.64/0.99  fof(f27,plain,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.64/0.99    inference(ennf_transformation,[],[f8])).
% 4.64/0.99  fof(f8,axiom,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 4.64/0.99  fof(f41,plain,(
% 4.64/0.99    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 4.64/0.99    inference(cnf_transformation,[],[f35])).
% 4.64/0.99  fof(f2608,plain,(
% 4.64/0.99    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k3_relat_1(sK1))),
% 4.64/0.99    inference(resolution,[],[f2397,f623])).
% 4.64/0.99  fof(f623,plain,(
% 4.64/0.99    r1_tarski(k4_xboole_0(k3_relat_1(sK0),k1_relat_1(sK0)),k2_relat_1(sK0))),
% 4.64/0.99    inference(resolution,[],[f144,f55])).
% 4.64/0.99  fof(f144,plain,(
% 4.64/0.99    ( ! [X2] : (~r1_tarski(X2,k3_relat_1(sK0)) | r1_tarski(k4_xboole_0(X2,k1_relat_1(sK0)),k2_relat_1(sK0))) )),
% 4.64/0.99    inference(superposition,[],[f50,f60])).
% 4.64/0.99  fof(f60,plain,(
% 4.64/0.99    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 4.64/0.99    inference(resolution,[],[f38,f42])).
% 4.64/0.99  fof(f50,plain,(
% 4.64/0.99    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.64/0.99    inference(cnf_transformation,[],[f29])).
% 4.64/0.99  fof(f29,plain,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.64/0.99    inference(ennf_transformation,[],[f11])).
% 4.64/0.99  fof(f11,axiom,(
% 4.64/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.64/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 4.64/0.99  fof(f2397,plain,(
% 4.64/0.99    ( ! [X4] : (~r1_tarski(X4,k2_relat_1(sK0)) | r1_tarski(X4,k3_relat_1(sK1))) )),
% 4.64/0.99    inference(superposition,[],[f51,f1880])).
% 4.64/1.00  % (1172)Time limit reached!
% 4.64/1.00  % (1172)------------------------------
% 4.64/1.00  % (1172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.00  fof(f1880,plain,(
% 4.64/1.00    k3_relat_1(sK1) = k2_xboole_0(k3_relat_1(sK1),k2_relat_1(sK0))),
% 4.64/1.00    inference(superposition,[],[f205,f47])).
% 4.64/1.00  fof(f205,plain,(
% 4.64/1.00    k3_relat_1(sK1) = k2_xboole_0(k2_relat_1(sK0),k3_relat_1(sK1))),
% 4.64/1.00    inference(resolution,[],[f199,f46])).
% 4.64/1.00  fof(f199,plain,(
% 4.64/1.00    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 4.64/1.00    inference(subsumption_resolution,[],[f194,f39])).
% 4.64/1.00  fof(f194,plain,(
% 4.64/1.00    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 4.64/1.00    inference(superposition,[],[f102,f42])).
% 4.64/1.00  fof(f102,plain,(
% 4.64/1.00    ( ! [X0] : (r1_tarski(k2_relat_1(sK0),k2_xboole_0(X0,k2_relat_1(sK1)))) )),
% 4.64/1.00    inference(resolution,[],[f75,f51])).
% 4.64/1.00  fof(f75,plain,(
% 4.64/1.00    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 4.64/1.00    inference(subsumption_resolution,[],[f74,f38])).
% 4.64/1.00  fof(f74,plain,(
% 4.64/1.00    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK0)),
% 4.64/1.00    inference(subsumption_resolution,[],[f67,f39])).
% 4.64/1.00  fof(f67,plain,(
% 4.64/1.00    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0)),
% 4.64/1.00    inference(resolution,[],[f40,f53])).
% 4.64/1.00  fof(f53,plain,(
% 4.64/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.64/1.00    inference(cnf_transformation,[],[f32])).
% 4.64/1.00  % SZS output end Proof for theBenchmark
% 4.64/1.00  % (1199)------------------------------
% 4.64/1.00  % (1199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.00  % (1199)Termination reason: Refutation
% 4.64/1.00  % (1151)Time limit reached!
% 4.64/1.00  % (1151)------------------------------
% 4.64/1.00  % (1151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.64/1.00  % (1151)Termination reason: Time limit
% 4.64/1.00  
% 4.64/1.00  % (1151)Memory used [KB]: 11513
% 4.64/1.00  % (1151)Time elapsed: 0.614 s
% 4.64/1.00  % (1151)------------------------------
% 4.64/1.00  % (1151)------------------------------
% 4.64/1.00  
% 4.64/1.00  % (1199)Memory used [KB]: 8571
% 4.64/1.00  % (1199)Time elapsed: 0.350 s
% 4.64/1.00  % (1199)------------------------------
% 4.64/1.00  % (1199)------------------------------
% 4.64/1.00  % (1143)Success in time 0.664 s
%------------------------------------------------------------------------------
