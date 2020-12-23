%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 152 expanded)
%              Number of leaves         :   11 (  38 expanded)
%              Depth                    :   19
%              Number of atoms          :  157 ( 448 expanded)
%              Number of equality atoms :   66 ( 188 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1098,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1080,f45])).

fof(f45,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1080,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(superposition,[],[f25,f1025])).

fof(f1025,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f1005,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1005,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f25,f932])).

fof(f932,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f858,f483])).

fof(f483,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f299,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f58,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(extensionality_resolution,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f299,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f278,f85])).

fof(f85,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0)
      | r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f39,f45])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f278,plain,(
    r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0) ),
    inference(superposition,[],[f107,f54])).

fof(f54,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f34,f24])).

fof(f24,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,(
    ! [X14,X17,X15,X16] : r1_tarski(k2_zfmisc_1(k4_xboole_0(X14,X15),X16),k4_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X17))) ),
    inference(superposition,[],[f28,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f858,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f835,f26])).

fof(f26,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f835,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f589,f65])).

fof(f589,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f588,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0)
      | r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f40,f44])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f588,plain,(
    r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f583,f27])).

fof(f583,plain,
    ( r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f423,f46])).

fof(f46,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f423,plain,(
    ! [X0] :
      ( r1_tarski(k2_xboole_0(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f397,f303])).

fof(f303,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f278,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f32,f27])).

fof(f397,plain,(
    ! [X0] :
      ( r1_tarski(k2_xboole_0(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),k1_xboole_0)
      | ~ r1_tarski(X0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)) ) ),
    inference(superposition,[],[f105,f54])).

fof(f105,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( r1_tarski(k2_xboole_0(X8,k2_zfmisc_1(X4,k4_xboole_0(X6,X7))),k4_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7)))
      | ~ r1_tarski(X8,k2_zfmisc_1(k4_xboole_0(X4,X5),X6)) ) ),
    inference(superposition,[],[f38,f41])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f25,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (6401)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.47  % (6393)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (6390)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (6384)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (6386)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (6380)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (6378)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6383)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (6388)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (6382)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (6377)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (6399)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (6395)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (6404)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (6400)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (6385)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (6389)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (6394)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (6397)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  % (6391)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (6392)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (6398)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (6379)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (6403)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.53  % (6402)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (6396)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.56  % (6395)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f1098,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(subsumption_resolution,[],[f1080,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f36])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.56    inference(flattening,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.56  fof(f1080,plain,(
% 0.20/0.56    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 0.20/0.56    inference(superposition,[],[f25,f1025])).
% 0.20/0.56  fof(f1025,plain,(
% 0.20/0.56    k1_xboole_0 = sK0),
% 0.20/0.56    inference(subsumption_resolution,[],[f1005,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.56    inference(equality_resolution,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f1005,plain,(
% 0.20/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.57    inference(superposition,[],[f25,f932])).
% 0.20/0.57  fof(f932,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(resolution,[],[f858,f483])).
% 0.20/0.57  fof(f483,plain,(
% 0.20/0.57    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 0.20/0.57    inference(resolution,[],[f299,f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(subsumption_resolution,[],[f58,f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(extensionality_resolution,[],[f32,f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(flattening,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.57  fof(f299,plain,(
% 0.20/0.57    r1_tarski(k4_xboole_0(sK0,sK2),k1_xboole_0) | k1_xboole_0 = sK1),
% 0.20/0.57    inference(resolution,[],[f278,f85])).
% 0.20/0.57  fof(f85,plain,(
% 0.20/0.57    ( ! [X2,X3] : (~r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0) | r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X2) )),
% 0.20/0.57    inference(superposition,[],[f39,f45])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 0.20/0.57  fof(f278,plain,(
% 0.20/0.57    r1_tarski(k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1),k1_xboole_0)),
% 0.20/0.57    inference(superposition,[],[f107,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    inference(resolution,[],[f34,f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f13,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.57    inference(flattening,[],[f12])).
% 0.20/0.57  fof(f12,plain,(
% 0.20/0.57    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    inference(negated_conjecture,[],[f10])).
% 0.20/0.57  fof(f10,conjecture,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f107,plain,(
% 0.20/0.57    ( ! [X14,X17,X15,X16] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(X14,X15),X16),k4_xboole_0(k2_zfmisc_1(X14,X16),k2_zfmisc_1(X15,X17)))) )),
% 0.20/0.57    inference(superposition,[],[f28,f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k4_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) = k2_xboole_0(k2_zfmisc_1(k4_xboole_0(X0,X2),X1),k2_zfmisc_1(X0,k4_xboole_0(X1,X3)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_zfmisc_1)).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.57  fof(f858,plain,(
% 0.20/0.57    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 0.20/0.57    inference(resolution,[],[f835,f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  fof(f835,plain,(
% 0.20/0.57    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 0.20/0.57    inference(resolution,[],[f589,f65])).
% 0.20/0.57  fof(f589,plain,(
% 0.20/0.57    r1_tarski(k4_xboole_0(sK1,sK3),k1_xboole_0) | k1_xboole_0 = sK0),
% 0.20/0.57    inference(resolution,[],[f588,f91])).
% 0.20/0.57  fof(f91,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k1_xboole_0) | r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(superposition,[],[f40,f44])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f588,plain,(
% 0.20/0.57    r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k1_xboole_0)),
% 0.20/0.57    inference(subsumption_resolution,[],[f583,f27])).
% 0.20/0.57  fof(f583,plain,(
% 0.20/0.57    r1_tarski(k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.57    inference(superposition,[],[f423,f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.57    inference(resolution,[],[f29,f27])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.57  fof(f423,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(forward_demodulation,[],[f397,f303])).
% 0.20/0.57  fof(f303,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 0.20/0.57    inference(resolution,[],[f278,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(resolution,[],[f32,f27])).
% 0.20/0.57  fof(f397,plain,(
% 0.20/0.57    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),k1_xboole_0) | ~r1_tarski(X0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1))) )),
% 0.20/0.57    inference(superposition,[],[f105,f54])).
% 0.20/0.57  fof(f105,plain,(
% 0.20/0.57    ( ! [X6,X4,X8,X7,X5] : (r1_tarski(k2_xboole_0(X8,k2_zfmisc_1(X4,k4_xboole_0(X6,X7))),k4_xboole_0(k2_zfmisc_1(X4,X6),k2_zfmisc_1(X5,X7))) | ~r1_tarski(X8,k2_zfmisc_1(k4_xboole_0(X4,X5),X6))) )),
% 0.20/0.57    inference(superposition,[],[f38,f41])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f15])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f18])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (6395)------------------------------
% 0.20/0.57  % (6395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (6395)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (6395)Memory used [KB]: 2174
% 0.20/0.57  % (6395)Time elapsed: 0.145 s
% 0.20/0.57  % (6395)------------------------------
% 0.20/0.57  % (6395)------------------------------
% 0.20/0.58  % (6375)Success in time 0.217 s
%------------------------------------------------------------------------------
