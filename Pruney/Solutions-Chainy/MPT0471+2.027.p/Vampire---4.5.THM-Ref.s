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
% DateTime   : Thu Dec  3 12:48:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  51 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 (  99 expanded)
%              Number of equality atoms :   58 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (9308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f54,plain,(
    $false ),
    inference(subsumption_resolution,[],[f53,f23])).

fof(f23,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f11])).

fof(f11,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

fof(f53,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f52,f45])).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f44,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f52,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f51,f25])).

fof(f25,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f51,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f50,f27])).

fof(f50,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f49,f24])).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f48,f42])).

fof(f42,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f32,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f32,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(resolution,[],[f38,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f28,f33])).

fof(f28,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:35:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (9306)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (9294)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (9292)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (9298)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (9296)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (9295)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (9314)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (9316)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (9293)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (9297)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (9295)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  % (9308)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f53,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,negated_conjecture,(
% 0.22/0.54    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(negated_conjecture,[],[f10])).
% 0.22/0.54  fof(f10,conjecture,(
% 0.22/0.54    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(forward_demodulation,[],[f52,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.22/0.54    inference(forward_demodulation,[],[f44,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.22/0.54    inference(resolution,[],[f39,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f34,f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    inference(forward_demodulation,[],[f51,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.22/0.54    inference(forward_demodulation,[],[f50,f27])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))),
% 0.22/0.54    inference(forward_demodulation,[],[f49,f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f9])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))),
% 0.22/0.54    inference(resolution,[],[f48,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f32,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(flattening,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.22/0.54    inference(resolution,[],[f38,f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f19,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(rectify,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f28,f33])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (9295)------------------------------
% 0.22/0.54  % (9295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (9295)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (9295)Memory used [KB]: 10618
% 0.22/0.54  % (9295)Time elapsed: 0.123 s
% 0.22/0.54  % (9295)------------------------------
% 0.22/0.54  % (9295)------------------------------
% 0.22/0.54  % (9291)Success in time 0.175 s
%------------------------------------------------------------------------------
