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
% DateTime   : Thu Dec  3 12:48:08 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :   84 (  86 expanded)
%              Number of equality atoms :   55 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f21,f48])).

fof(f48,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f47,f25])).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f47,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f46,f23])).

fof(f23,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f46,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f45,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f45,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f43,f22])).

fof(f22,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) ),
    inference(resolution,[],[f42,f38])).

fof(f38,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f30,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ( ! [X2,X3] : k4_tarski(X2,X3) != sK0(X0)
          & r2_hidden(sK0(X0),X0) ) )
      & ( ! [X4] :
            ( k4_tarski(sK1(X4),sK2(X4)) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK0(X0)
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X4] :
      ( ? [X5,X6] : k4_tarski(X5,X6) = X4
     => k4_tarski(sK1(X4),sK2(X4)) = X4 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X4] :
            ( ? [X5,X6] : k4_tarski(X5,X6) = X4
            | ~ r2_hidden(X4,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        | ? [X1] :
            ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( ? [X2,X3] : k4_tarski(X2,X3) = X1
            | ~ r2_hidden(X1,X0) )
        | ~ v1_relat_1(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f26,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f21,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f10])).

fof(f10,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:06:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.36  ipcrm: permission denied for id (800129024)
% 0.12/0.37  ipcrm: permission denied for id (800325639)
% 0.12/0.37  ipcrm: permission denied for id (800358408)
% 0.12/0.37  ipcrm: permission denied for id (800555022)
% 0.12/0.38  ipcrm: permission denied for id (800620560)
% 0.12/0.38  ipcrm: permission denied for id (800686098)
% 0.12/0.38  ipcrm: permission denied for id (800751637)
% 0.12/0.38  ipcrm: permission denied for id (800784406)
% 0.20/0.39  ipcrm: permission denied for id (800849946)
% 0.20/0.39  ipcrm: permission denied for id (800915486)
% 0.20/0.40  ipcrm: permission denied for id (800948257)
% 0.20/0.40  ipcrm: permission denied for id (800981027)
% 0.20/0.40  ipcrm: permission denied for id (801013796)
% 0.20/0.40  ipcrm: permission denied for id (801046565)
% 0.20/0.40  ipcrm: permission denied for id (801079334)
% 0.20/0.40  ipcrm: permission denied for id (801112103)
% 0.20/0.40  ipcrm: permission denied for id (801144872)
% 0.20/0.40  ipcrm: permission denied for id (801177641)
% 0.20/0.41  ipcrm: permission denied for id (801210410)
% 0.20/0.41  ipcrm: permission denied for id (801243179)
% 0.20/0.41  ipcrm: permission denied for id (801275948)
% 0.20/0.41  ipcrm: permission denied for id (801308717)
% 0.20/0.41  ipcrm: permission denied for id (801374255)
% 0.20/0.41  ipcrm: permission denied for id (801439793)
% 0.20/0.42  ipcrm: permission denied for id (801701945)
% 0.20/0.42  ipcrm: permission denied for id (801734714)
% 0.20/0.42  ipcrm: permission denied for id (801767483)
% 0.20/0.43  ipcrm: permission denied for id (801865790)
% 0.20/0.43  ipcrm: permission denied for id (801931328)
% 0.20/0.43  ipcrm: permission denied for id (802029636)
% 0.20/0.44  ipcrm: permission denied for id (802193482)
% 0.20/0.45  ipcrm: permission denied for id (802324558)
% 0.20/0.45  ipcrm: permission denied for id (802357327)
% 0.20/0.45  ipcrm: permission denied for id (802488402)
% 0.20/0.45  ipcrm: permission denied for id (802521171)
% 0.20/0.45  ipcrm: permission denied for id (802586709)
% 0.20/0.46  ipcrm: permission denied for id (802685015)
% 0.20/0.46  ipcrm: permission denied for id (802783323)
% 0.20/0.46  ipcrm: permission denied for id (802816092)
% 0.20/0.46  ipcrm: permission denied for id (802848861)
% 0.20/0.47  ipcrm: permission denied for id (802914399)
% 0.20/0.47  ipcrm: permission denied for id (802947168)
% 0.20/0.47  ipcrm: permission denied for id (803012706)
% 0.20/0.47  ipcrm: permission denied for id (803078244)
% 0.20/0.47  ipcrm: permission denied for id (803143783)
% 0.20/0.48  ipcrm: permission denied for id (803176553)
% 0.20/0.48  ipcrm: permission denied for id (803209322)
% 0.20/0.48  ipcrm: permission denied for id (803340398)
% 0.20/0.49  ipcrm: permission denied for id (803405937)
% 0.20/0.49  ipcrm: permission denied for id (803471475)
% 0.20/0.50  ipcrm: permission denied for id (803602553)
% 0.20/0.50  ipcrm: permission denied for id (803635322)
% 0.20/0.50  ipcrm: permission denied for id (803668091)
% 0.20/0.50  ipcrm: permission denied for id (803700860)
% 0.20/0.50  ipcrm: permission denied for id (803733629)
% 0.38/0.62  % (12609)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.42/0.64  % (12619)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.42/0.64  % (12627)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.42/0.64  % (12609)Refutation not found, incomplete strategy% (12609)------------------------------
% 0.42/0.64  % (12609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.42/0.65  % (12635)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.42/0.65  % (12609)Termination reason: Refutation not found, incomplete strategy
% 0.42/0.65  
% 0.42/0.65  % (12609)Memory used [KB]: 10618
% 0.42/0.65  % (12609)Time elapsed: 0.092 s
% 0.42/0.65  % (12609)------------------------------
% 0.42/0.65  % (12609)------------------------------
% 0.42/0.65  % (12616)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.42/0.65  % (12627)Refutation not found, incomplete strategy% (12627)------------------------------
% 0.42/0.65  % (12627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.42/0.65  % (12627)Termination reason: Refutation not found, incomplete strategy
% 0.42/0.65  
% 0.42/0.65  % (12627)Memory used [KB]: 10618
% 0.42/0.65  % (12627)Time elapsed: 0.105 s
% 0.42/0.65  % (12627)------------------------------
% 0.42/0.65  % (12627)------------------------------
% 0.42/0.65  % (12619)Refutation found. Thanks to Tanya!
% 0.42/0.65  % SZS status Theorem for theBenchmark
% 0.42/0.65  % SZS output start Proof for theBenchmark
% 0.42/0.65  fof(f50,plain,(
% 0.42/0.65    $false),
% 0.42/0.65    inference(trivial_inequality_removal,[],[f49])).
% 0.42/0.65  fof(f49,plain,(
% 0.42/0.65    k1_xboole_0 != k1_xboole_0),
% 0.42/0.65    inference(superposition,[],[f21,f48])).
% 0.42/0.65  fof(f48,plain,(
% 0.42/0.65    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.42/0.65    inference(forward_demodulation,[],[f47,f25])).
% 0.42/0.65  fof(f25,plain,(
% 0.42/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.42/0.65    inference(cnf_transformation,[],[f2])).
% 0.42/0.65  fof(f2,axiom,(
% 0.42/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.42/0.65  fof(f47,plain,(
% 0.42/0.65    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.42/0.65    inference(forward_demodulation,[],[f46,f23])).
% 0.42/0.65  fof(f23,plain,(
% 0.42/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.42/0.65    inference(cnf_transformation,[],[f8])).
% 0.42/0.65  fof(f8,axiom,(
% 0.42/0.65    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.42/0.65  fof(f46,plain,(
% 0.42/0.65    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))),
% 0.42/0.65    inference(forward_demodulation,[],[f45,f24])).
% 0.42/0.65  fof(f24,plain,(
% 0.42/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.42/0.65    inference(cnf_transformation,[],[f1])).
% 0.42/0.65  fof(f1,axiom,(
% 0.42/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.42/0.65  fof(f45,plain,(
% 0.42/0.65    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))),
% 0.42/0.65    inference(forward_demodulation,[],[f43,f22])).
% 0.42/0.65  fof(f22,plain,(
% 0.42/0.65    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.42/0.65    inference(cnf_transformation,[],[f8])).
% 0.42/0.65  fof(f43,plain,(
% 0.42/0.65    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))),
% 0.42/0.65    inference(resolution,[],[f42,f38])).
% 0.42/0.65  fof(f38,plain,(
% 0.42/0.65    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.42/0.65    inference(superposition,[],[f30,f36])).
% 0.42/0.65  fof(f36,plain,(
% 0.42/0.65    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.42/0.65    inference(equality_resolution,[],[f34])).
% 0.42/0.65  fof(f34,plain,(
% 0.42/0.65    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.42/0.65    inference(cnf_transformation,[],[f20])).
% 0.42/0.65  fof(f20,plain,(
% 0.42/0.65    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.42/0.65    inference(flattening,[],[f19])).
% 0.42/0.65  fof(f19,plain,(
% 0.42/0.65    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.42/0.65    inference(nnf_transformation,[],[f4])).
% 0.42/0.65  fof(f4,axiom,(
% 0.42/0.65    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.42/0.65  fof(f30,plain,(
% 0.42/0.65    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.42/0.65    inference(cnf_transformation,[],[f5])).
% 0.42/0.65  fof(f5,axiom,(
% 0.42/0.65    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.42/0.65  fof(f42,plain,(
% 0.42/0.65    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.42/0.65    inference(resolution,[],[f35,f28])).
% 0.42/0.65  fof(f28,plain,(
% 0.42/0.65    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK0(X0),X0)) )),
% 0.42/0.65    inference(cnf_transformation,[],[f18])).
% 0.42/0.65  fof(f18,plain,(
% 0.42/0.65    ! [X0] : ((v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0))) & (! [X4] : (k4_tarski(sK1(X4),sK2(X4)) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.42/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f17,f16])).
% 0.42/0.65  fof(f16,plain,(
% 0.42/0.65    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK0(X0) & r2_hidden(sK0(X0),X0)))),
% 0.42/0.65    introduced(choice_axiom,[])).
% 0.42/0.65  fof(f17,plain,(
% 0.42/0.65    ! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 => k4_tarski(sK1(X4),sK2(X4)) = X4)),
% 0.42/0.65    introduced(choice_axiom,[])).
% 0.42/0.65  fof(f15,plain,(
% 0.42/0.65    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X4] : (? [X5,X6] : k4_tarski(X5,X6) = X4 | ~r2_hidden(X4,X0)) | ~v1_relat_1(X0)))),
% 0.42/0.65    inference(rectify,[],[f14])).
% 0.42/0.65  fof(f14,plain,(
% 0.42/0.65    ! [X0] : ((v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0))) & (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0)))),
% 0.42/0.65    inference(nnf_transformation,[],[f13])).
% 0.42/0.65  fof(f13,plain,(
% 0.42/0.65    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.42/0.65    inference(ennf_transformation,[],[f6])).
% 0.42/0.65  fof(f6,axiom,(
% 0.42/0.65    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.42/0.65  fof(f35,plain,(
% 0.42/0.65    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.42/0.65    inference(definition_unfolding,[],[f26,f31])).
% 0.42/0.65  fof(f31,plain,(
% 0.42/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.42/0.65    inference(cnf_transformation,[],[f3])).
% 0.42/0.65  fof(f3,axiom,(
% 0.42/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.42/0.65  fof(f26,plain,(
% 0.42/0.65    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.42/0.65    inference(cnf_transformation,[],[f12])).
% 0.42/0.65  fof(f12,plain,(
% 0.42/0.65    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.42/0.65    inference(ennf_transformation,[],[f7])).
% 0.42/0.65  fof(f7,axiom,(
% 0.42/0.65    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.42/0.65  fof(f21,plain,(
% 0.42/0.65    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.42/0.65    inference(cnf_transformation,[],[f11])).
% 0.42/0.65  fof(f11,plain,(
% 0.42/0.65    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.42/0.65    inference(flattening,[],[f10])).
% 0.42/0.65  fof(f10,negated_conjecture,(
% 0.42/0.65    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.42/0.65    inference(negated_conjecture,[],[f9])).
% 0.42/0.65  fof(f9,conjecture,(
% 0.42/0.65    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.42/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.42/0.65  % SZS output end Proof for theBenchmark
% 0.42/0.65  % (12619)------------------------------
% 0.42/0.65  % (12619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.42/0.65  % (12619)Termination reason: Refutation
% 0.42/0.65  
% 0.42/0.65  % (12619)Memory used [KB]: 6140
% 0.42/0.65  % (12619)Time elapsed: 0.107 s
% 0.42/0.65  % (12619)------------------------------
% 0.42/0.65  % (12619)------------------------------
% 0.42/0.65  % (12472)Success in time 0.3 s
%------------------------------------------------------------------------------
