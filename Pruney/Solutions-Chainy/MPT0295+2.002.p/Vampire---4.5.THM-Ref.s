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
% DateTime   : Thu Dec  3 12:41:49 EST 2020

% Result     : Theorem 14.50s
% Output     : Refutation 14.50s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 105 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :   16
%              Number of atoms          :  151 ( 247 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16628,plain,(
    $false ),
    inference(resolution,[],[f16623,f12642])).

fof(f12642,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f656,f86])).

fof(f86,plain,(
    ! [X0] :
      ( r1_xboole_0(k2_tarski(sK3,sK3),X0)
      | ~ r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f72,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f72,plain,(
    r1_tarski(k2_tarski(sK3,sK3),sK0) ),
    inference(resolution,[],[f27,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f53,f60])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f27,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4,X5] :
          ( k4_tarski(X4,X5) != X3
          | ~ r2_hidden(X5,X2)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X3,X0)
      & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4,X5] :
              ~ ( k4_tarski(X4,X5) = X3
                & r2_hidden(X5,X2)
                & r2_hidden(X4,X1) )
          & r2_hidden(X3,X0)
          & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f656,plain,(
    ! [X0] : ~ r1_xboole_0(k2_tarski(sK3,X0),k4_xboole_0(sK0,k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f615,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f615,plain,(
    r2_hidden(sK3,k4_xboole_0(sK0,k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f507,f176])).

fof(f176,plain,(
    ! [X5] :
      ( r2_hidden(sK3,k4_xboole_0(X5,k4_xboole_0(X5,sK0)))
      | r2_hidden(sK3,k4_xboole_0(sK0,X5)) ) ),
    inference(superposition,[],[f101,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f43,f40,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f101,plain,(
    ! [X2] :
      ( r2_hidden(sK3,k4_xboole_0(sK0,X2))
      | r2_hidden(sK3,X2) ) ),
    inference(resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f76,plain,(
    ! [X5] :
      ( sP5(sK3,X5,sK0)
      | r2_hidden(sK3,X5) ) ),
    inference(resolution,[],[f27,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f507,plain,(
    ! [X1] : ~ r2_hidden(sK3,k4_xboole_0(k2_zfmisc_1(sK1,sK2),X1)) ),
    inference(resolution,[],[f485,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f485,plain,(
    ! [X1] : ~ sP5(sK3,X1,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f477,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f477,plain,(
    ~ r2_hidden(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f472,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f472,plain,(
    ~ sP7(sK3,sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,
    ( ~ sP7(sK3,sK2,sK1)
    | ~ sP7(sK3,sK2,sK1) ),
    inference(resolution,[],[f284,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X0)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f284,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(X0,sK2,sK3),sK1)
      | ~ sP7(sK3,sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(X0,sK2,sK3),sK1)
      | ~ sP7(sK3,sK2,X0)
      | ~ sP7(sK3,sK2,X0) ) ),
    inference(resolution,[],[f153,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK9(X0,X1,X3),X1)
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1,sK3),sK2)
      | ~ r2_hidden(sK8(X0,X1,sK3),sK1)
      | ~ sP7(sK3,X1,X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sK3 != X2
      | ~ r2_hidden(sK9(X0,X1,X2),sK2)
      | ~ r2_hidden(sK8(X0,X1,X2),sK1)
      | ~ sP7(X2,X1,X0) ) ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3
      | ~ sP7(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f16623,plain,(
    ! [X0] : r1_xboole_0(sK0,k4_xboole_0(X0,k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f2176,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2176,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),X2)
      | r1_xboole_0(sK0,k4_xboole_0(X3,X2)) ) ),
    inference(forward_demodulation,[],[f2169,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2169,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X3,X2),X2))
      | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),X2) ) ),
    inference(superposition,[],[f702,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f702,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X0,X1),X0))
      | ~ r1_tarski(k2_zfmisc_1(sK1,sK2),X0) ) ),
    inference(superposition,[],[f192,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f192,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k4_xboole_0(X11,k4_xboole_0(X11,X10)))
      | r1_xboole_0(sK0,k4_xboole_0(X10,X11)) ) ),
    inference(superposition,[],[f108,f62])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(sK1,sK2),k4_xboole_0(X1,X0))
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_zfmisc_1(sK1,sK2),X0)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f26,f55])).

fof(f26,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n003.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 15:29:57 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.52  % (30214)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (30221)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (30215)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (30225)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (30217)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (30207)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (30222)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (30229)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (30213)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (30233)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (30221)Refutation not found, incomplete strategy% (30221)------------------------------
% 0.22/0.55  % (30221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (30221)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (30221)Memory used [KB]: 1791
% 0.22/0.55  % (30221)Time elapsed: 0.127 s
% 0.22/0.55  % (30221)------------------------------
% 0.22/0.55  % (30221)------------------------------
% 0.22/0.55  % (30218)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (30236)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (30231)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (30227)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (30208)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (30223)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (30230)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (30219)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (30223)Refutation not found, incomplete strategy% (30223)------------------------------
% 0.22/0.56  % (30223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (30223)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (30223)Memory used [KB]: 10618
% 0.22/0.56  % (30223)Time elapsed: 0.122 s
% 0.22/0.56  % (30223)------------------------------
% 0.22/0.56  % (30223)------------------------------
% 0.22/0.56  % (30210)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (30212)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.56  % (30226)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.57  % (30235)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.57  % (30228)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.57  % (30211)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.48/0.57  % (30234)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.57  % (30209)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.48/0.57  % (30220)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.58  % (30224)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.58  % (30216)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.59/0.59  % (30232)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.04/0.71  % (30210)Refutation not found, incomplete strategy% (30210)------------------------------
% 2.04/0.71  % (30210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.71  % (30210)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.71  
% 2.04/0.71  % (30210)Memory used [KB]: 6140
% 2.04/0.71  % (30210)Time elapsed: 0.261 s
% 2.04/0.71  % (30210)------------------------------
% 2.04/0.71  % (30210)------------------------------
% 2.04/0.71  % (30238)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.59/0.72  % (30237)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.99/0.83  % (30239)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.99/0.83  % (30231)Time limit reached!
% 2.99/0.83  % (30231)------------------------------
% 2.99/0.83  % (30231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.99/0.83  % (30231)Termination reason: Time limit
% 2.99/0.83  % (30231)Termination phase: Saturation
% 2.99/0.83  
% 2.99/0.83  % (30231)Memory used [KB]: 13432
% 2.99/0.83  % (30231)Time elapsed: 0.400 s
% 2.99/0.83  % (30231)------------------------------
% 2.99/0.83  % (30231)------------------------------
% 2.99/0.85  % (30209)Time limit reached!
% 2.99/0.85  % (30209)------------------------------
% 2.99/0.85  % (30209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.99/0.85  % (30209)Termination reason: Time limit
% 2.99/0.85  % (30209)Termination phase: Saturation
% 2.99/0.85  
% 2.99/0.85  % (30209)Memory used [KB]: 7036
% 2.99/0.85  % (30209)Time elapsed: 0.400 s
% 2.99/0.85  % (30209)------------------------------
% 2.99/0.85  % (30209)------------------------------
% 4.13/0.93  % (30236)Time limit reached!
% 4.13/0.93  % (30236)------------------------------
% 4.13/0.93  % (30236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.93  % (30236)Termination reason: Time limit
% 4.13/0.93  
% 4.13/0.93  % (30236)Memory used [KB]: 6396
% 4.13/0.93  % (30236)Time elapsed: 0.518 s
% 4.13/0.93  % (30236)------------------------------
% 4.13/0.93  % (30236)------------------------------
% 4.13/0.94  % (30213)Time limit reached!
% 4.13/0.94  % (30213)------------------------------
% 4.13/0.94  % (30213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.13/0.94  % (30213)Termination reason: Time limit
% 4.13/0.94  
% 4.13/0.94  % (30213)Memory used [KB]: 14072
% 4.13/0.94  % (30213)Time elapsed: 0.516 s
% 4.13/0.94  % (30213)------------------------------
% 4.13/0.94  % (30213)------------------------------
% 4.22/0.96  % (30240)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.22/0.98  % (30241)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.22/1.00  % (30241)Refutation not found, incomplete strategy% (30241)------------------------------
% 4.22/1.00  % (30241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.22/1.00  % (30241)Termination reason: Refutation not found, incomplete strategy
% 4.22/1.00  
% 4.22/1.00  % (30241)Memory used [KB]: 10746
% 4.22/1.00  % (30241)Time elapsed: 0.126 s
% 4.22/1.00  % (30241)------------------------------
% 4.22/1.00  % (30241)------------------------------
% 4.73/1.04  % (30214)Time limit reached!
% 4.73/1.04  % (30214)------------------------------
% 4.73/1.04  % (30214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.73/1.04  % (30214)Termination reason: Time limit
% 4.73/1.04  
% 4.73/1.04  % (30214)Memory used [KB]: 5628
% 4.73/1.04  % (30214)Time elapsed: 0.613 s
% 4.73/1.04  % (30214)------------------------------
% 4.73/1.04  % (30214)------------------------------
% 4.73/1.06  % (30242)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.73/1.08  % (30243)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.53/1.14  % (30244)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.40/1.20  % (30245)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 6.69/1.26  % (30208)Time limit reached!
% 6.69/1.26  % (30208)------------------------------
% 6.69/1.26  % (30208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.69/1.26  % (30208)Termination reason: Time limit
% 6.69/1.26  
% 6.69/1.26  % (30208)Memory used [KB]: 6780
% 6.69/1.26  % (30208)Time elapsed: 0.838 s
% 6.69/1.26  % (30208)------------------------------
% 6.69/1.26  % (30208)------------------------------
% 7.79/1.40  % (30246)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.79/1.45  % (30219)Time limit reached!
% 7.79/1.45  % (30219)------------------------------
% 7.79/1.45  % (30219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.79/1.45  % (30219)Termination reason: Time limit
% 7.79/1.45  
% 7.79/1.45  % (30219)Memory used [KB]: 15351
% 7.79/1.45  % (30219)Time elapsed: 1.030 s
% 7.79/1.45  % (30219)------------------------------
% 7.79/1.45  % (30219)------------------------------
% 8.54/1.47  % (30234)Time limit reached!
% 8.54/1.47  % (30234)------------------------------
% 8.54/1.47  % (30234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.54/1.47  % (30234)Termination reason: Time limit
% 8.54/1.47  % (30234)Termination phase: Saturation
% 8.54/1.47  
% 8.54/1.47  % (30234)Memory used [KB]: 9210
% 8.54/1.47  % (30234)Time elapsed: 1.0000 s
% 8.54/1.47  % (30234)------------------------------
% 8.54/1.47  % (30234)------------------------------
% 9.05/1.58  % (30239)Time limit reached!
% 9.05/1.58  % (30239)------------------------------
% 9.05/1.58  % (30239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.05/1.58  % (30239)Termination reason: Time limit
% 9.05/1.58  % (30239)Termination phase: Saturation
% 9.05/1.58  
% 9.05/1.58  % (30239)Memory used [KB]: 14328
% 9.05/1.58  % (30239)Time elapsed: 0.800 s
% 9.05/1.58  % (30239)------------------------------
% 9.05/1.58  % (30239)------------------------------
% 9.05/1.59  % (30247)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.71/1.62  % (30243)Time limit reached!
% 9.71/1.62  % (30243)------------------------------
% 9.71/1.62  % (30243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.71/1.62  % (30243)Termination reason: Time limit
% 9.71/1.62  
% 9.71/1.62  % (30243)Memory used [KB]: 18933
% 9.71/1.62  % (30243)Time elapsed: 0.633 s
% 9.71/1.62  % (30243)------------------------------
% 9.71/1.62  % (30243)------------------------------
% 9.71/1.63  % (30248)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.71/1.64  % (30207)Time limit reached!
% 9.71/1.64  % (30207)------------------------------
% 9.71/1.64  % (30207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.71/1.64  % (30207)Termination reason: Time limit
% 9.71/1.64  
% 9.71/1.64  % (30207)Memory used [KB]: 12153
% 9.71/1.64  % (30207)Time elapsed: 1.216 s
% 9.71/1.64  % (30207)------------------------------
% 9.71/1.64  % (30207)------------------------------
% 10.26/1.72  % (30212)Time limit reached!
% 10.26/1.72  % (30212)------------------------------
% 10.26/1.72  % (30212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.26/1.72  % (30212)Termination reason: Time limit
% 10.26/1.72  % (30212)Termination phase: Saturation
% 10.26/1.72  
% 10.26/1.72  % (30212)Memory used [KB]: 10362
% 10.26/1.72  % (30212)Time elapsed: 1.300 s
% 10.26/1.72  % (30212)------------------------------
% 10.26/1.72  % (30212)------------------------------
% 10.26/1.72  % (30249)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.26/1.77  % (30250)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 10.98/1.78  % (30251)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.30/1.86  % (30252)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.89/1.93  % (30251)Refutation not found, incomplete strategy% (30251)------------------------------
% 11.89/1.93  % (30251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.89/1.93  % (30251)Termination reason: Refutation not found, incomplete strategy
% 11.89/1.93  
% 11.89/1.93  % (30251)Memory used [KB]: 6268
% 11.89/1.93  % (30251)Time elapsed: 0.234 s
% 11.89/1.93  % (30251)------------------------------
% 11.89/1.93  % (30251)------------------------------
% 12.50/2.04  % (30233)Time limit reached!
% 12.50/2.04  % (30233)------------------------------
% 12.50/2.04  % (30233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.50/2.05  % (30233)Termination reason: Time limit
% 12.50/2.05  % (30233)Termination phase: Saturation
% 12.50/2.05  
% 12.50/2.05  % (30233)Memory used [KB]: 14456
% 12.50/2.05  % (30233)Time elapsed: 1.600 s
% 12.50/2.05  % (30233)------------------------------
% 12.50/2.05  % (30233)------------------------------
% 12.50/2.07  % (30253)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 12.50/2.07  % (30250)Time limit reached!
% 12.50/2.07  % (30250)------------------------------
% 12.50/2.07  % (30250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.18/2.09  % (30250)Termination reason: Time limit
% 13.18/2.09  % (30250)Termination phase: Saturation
% 13.18/2.09  
% 13.18/2.09  % (30250)Memory used [KB]: 13432
% 13.18/2.09  % (30250)Time elapsed: 0.400 s
% 13.18/2.09  % (30250)------------------------------
% 13.18/2.09  % (30250)------------------------------
% 13.18/2.09  % (30246)Time limit reached!
% 13.18/2.09  % (30246)------------------------------
% 13.18/2.09  % (30246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.42/2.11  % (30246)Termination reason: Time limit
% 13.42/2.11  
% 13.42/2.11  % (30246)Memory used [KB]: 17142
% 13.42/2.11  % (30246)Time elapsed: 0.812 s
% 13.42/2.11  % (30246)------------------------------
% 13.42/2.11  % (30246)------------------------------
% 13.85/2.16  % (30252)Time limit reached!
% 13.85/2.16  % (30252)------------------------------
% 13.85/2.16  % (30252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.85/2.16  % (30252)Termination reason: Time limit
% 13.85/2.16  
% 13.85/2.16  % (30252)Memory used [KB]: 8059
% 13.85/2.16  % (30252)Time elapsed: 0.421 s
% 13.85/2.16  % (30252)------------------------------
% 13.85/2.16  % (30252)------------------------------
% 13.85/2.18  % (30254)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 14.50/2.22  % (30255)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 14.50/2.24  % (30256)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 14.50/2.25  % (30242)Refutation found. Thanks to Tanya!
% 14.50/2.25  % SZS status Theorem for theBenchmark
% 14.50/2.26  % SZS output start Proof for theBenchmark
% 14.50/2.26  fof(f16628,plain,(
% 14.50/2.26    $false),
% 14.50/2.26    inference(resolution,[],[f16623,f12642])).
% 14.50/2.26  fof(f12642,plain,(
% 14.50/2.26    ~r1_xboole_0(sK0,k4_xboole_0(sK0,k2_zfmisc_1(sK1,sK2)))),
% 14.50/2.26    inference(resolution,[],[f656,f86])).
% 14.50/2.26  fof(f86,plain,(
% 14.50/2.26    ( ! [X0] : (r1_xboole_0(k2_tarski(sK3,sK3),X0) | ~r1_xboole_0(sK0,X0)) )),
% 14.50/2.26    inference(resolution,[],[f72,f55])).
% 14.50/2.26  fof(f55,plain,(
% 14.50/2.26    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f22])).
% 14.50/2.26  fof(f22,plain,(
% 14.50/2.26    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 14.50/2.26    inference(flattening,[],[f21])).
% 14.50/2.26  fof(f21,plain,(
% 14.50/2.26    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 14.50/2.26    inference(ennf_transformation,[],[f12])).
% 14.50/2.26  fof(f12,axiom,(
% 14.50/2.26    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 14.50/2.26  fof(f72,plain,(
% 14.50/2.26    r1_tarski(k2_tarski(sK3,sK3),sK0)),
% 14.50/2.26    inference(resolution,[],[f27,f64])).
% 14.50/2.26  fof(f64,plain,(
% 14.50/2.26    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k2_tarski(X0,X0),X1)) )),
% 14.50/2.26    inference(definition_unfolding,[],[f53,f60])).
% 14.50/2.26  fof(f60,plain,(
% 14.50/2.26    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f13])).
% 14.50/2.26  fof(f13,axiom,(
% 14.50/2.26    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 14.50/2.26  fof(f53,plain,(
% 14.50/2.26    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f15])).
% 14.50/2.26  fof(f15,axiom,(
% 14.50/2.26    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 14.50/2.26  fof(f27,plain,(
% 14.50/2.26    r2_hidden(sK3,sK0)),
% 14.50/2.26    inference(cnf_transformation,[],[f19])).
% 14.50/2.26  fof(f19,plain,(
% 14.50/2.26    ? [X0,X1,X2,X3] : (! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X2) | ~r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 14.50/2.26    inference(ennf_transformation,[],[f18])).
% 14.50/2.26  fof(f18,negated_conjecture,(
% 14.50/2.26    ~! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 14.50/2.26    inference(negated_conjecture,[],[f17])).
% 14.50/2.26  fof(f17,conjecture,(
% 14.50/2.26    ! [X0,X1,X2,X3] : ~(! [X4,X5] : ~(k4_tarski(X4,X5) = X3 & r2_hidden(X5,X2) & r2_hidden(X4,X1)) & r2_hidden(X3,X0) & r1_tarski(X0,k2_zfmisc_1(X1,X2)))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).
% 14.50/2.26  fof(f656,plain,(
% 14.50/2.26    ( ! [X0] : (~r1_xboole_0(k2_tarski(sK3,X0),k4_xboole_0(sK0,k2_zfmisc_1(sK1,sK2)))) )),
% 14.50/2.26    inference(resolution,[],[f615,f52])).
% 14.50/2.26  fof(f52,plain,(
% 14.50/2.26    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f20])).
% 14.50/2.26  fof(f20,plain,(
% 14.50/2.26    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 14.50/2.26    inference(ennf_transformation,[],[f16])).
% 14.50/2.26  fof(f16,axiom,(
% 14.50/2.26    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 14.50/2.26  fof(f615,plain,(
% 14.50/2.26    r2_hidden(sK3,k4_xboole_0(sK0,k2_zfmisc_1(sK1,sK2)))),
% 14.50/2.26    inference(resolution,[],[f507,f176])).
% 14.50/2.26  fof(f176,plain,(
% 14.50/2.26    ( ! [X5] : (r2_hidden(sK3,k4_xboole_0(X5,k4_xboole_0(X5,sK0))) | r2_hidden(sK3,k4_xboole_0(sK0,X5))) )),
% 14.50/2.26    inference(superposition,[],[f101,f62])).
% 14.50/2.26  fof(f62,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 14.50/2.26    inference(definition_unfolding,[],[f43,f40,f40])).
% 14.50/2.26  fof(f40,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 14.50/2.26    inference(cnf_transformation,[],[f11])).
% 14.50/2.26  fof(f11,axiom,(
% 14.50/2.26    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 14.50/2.26  fof(f43,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f2])).
% 14.50/2.26  fof(f2,axiom,(
% 14.50/2.26    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 14.50/2.26  fof(f101,plain,(
% 14.50/2.26    ( ! [X2] : (r2_hidden(sK3,k4_xboole_0(sK0,X2)) | r2_hidden(sK3,X2)) )),
% 14.50/2.26    inference(resolution,[],[f76,f66])).
% 14.50/2.26  fof(f66,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 14.50/2.26    inference(equality_resolution,[],[f31])).
% 14.50/2.26  fof(f31,plain,(
% 14.50/2.26    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.50/2.26    inference(cnf_transformation,[],[f3])).
% 14.50/2.26  fof(f3,axiom,(
% 14.50/2.26    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 14.50/2.26  fof(f76,plain,(
% 14.50/2.26    ( ! [X5] : (sP5(sK3,X5,sK0) | r2_hidden(sK3,X5)) )),
% 14.50/2.26    inference(resolution,[],[f27,f28])).
% 14.50/2.26  fof(f28,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | sP5(X3,X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f3])).
% 14.50/2.26  fof(f507,plain,(
% 14.50/2.26    ( ! [X1] : (~r2_hidden(sK3,k4_xboole_0(k2_zfmisc_1(sK1,sK2),X1))) )),
% 14.50/2.26    inference(resolution,[],[f485,f65])).
% 14.50/2.26  fof(f65,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 14.50/2.26    inference(equality_resolution,[],[f32])).
% 14.50/2.26  fof(f32,plain,(
% 14.50/2.26    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 14.50/2.26    inference(cnf_transformation,[],[f3])).
% 14.50/2.26  fof(f485,plain,(
% 14.50/2.26    ( ! [X1] : (~sP5(sK3,X1,k2_zfmisc_1(sK1,sK2))) )),
% 14.50/2.26    inference(resolution,[],[f477,f29])).
% 14.50/2.26  fof(f29,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~sP5(X3,X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f3])).
% 14.50/2.26  fof(f477,plain,(
% 14.50/2.26    ~r2_hidden(sK3,k2_zfmisc_1(sK1,sK2))),
% 14.50/2.26    inference(resolution,[],[f472,f69])).
% 14.50/2.26  fof(f69,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 14.50/2.26    inference(equality_resolution,[],[f49])).
% 14.50/2.26  fof(f49,plain,(
% 14.50/2.26    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 14.50/2.26    inference(cnf_transformation,[],[f14])).
% 14.50/2.26  fof(f14,axiom,(
% 14.50/2.26    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 14.50/2.26  fof(f472,plain,(
% 14.50/2.26    ~sP7(sK3,sK2,sK1)),
% 14.50/2.26    inference(duplicate_literal_removal,[],[f468])).
% 14.50/2.26  fof(f468,plain,(
% 14.50/2.26    ~sP7(sK3,sK2,sK1) | ~sP7(sK3,sK2,sK1)),
% 14.50/2.26    inference(resolution,[],[f284,f45])).
% 14.50/2.26  fof(f45,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X0) | ~sP7(X3,X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f14])).
% 14.50/2.26  fof(f284,plain,(
% 14.50/2.26    ( ! [X0] : (~r2_hidden(sK8(X0,sK2,sK3),sK1) | ~sP7(sK3,sK2,X0)) )),
% 14.50/2.26    inference(duplicate_literal_removal,[],[f280])).
% 14.50/2.26  fof(f280,plain,(
% 14.50/2.26    ( ! [X0] : (~r2_hidden(sK8(X0,sK2,sK3),sK1) | ~sP7(sK3,sK2,X0) | ~sP7(sK3,sK2,X0)) )),
% 14.50/2.26    inference(resolution,[],[f153,f46])).
% 14.50/2.26  fof(f46,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (r2_hidden(sK9(X0,X1,X3),X1) | ~sP7(X3,X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f14])).
% 14.50/2.26  fof(f153,plain,(
% 14.50/2.26    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1,sK3),sK2) | ~r2_hidden(sK8(X0,X1,sK3),sK1) | ~sP7(sK3,X1,X0)) )),
% 14.50/2.26    inference(equality_resolution,[],[f89])).
% 14.50/2.26  fof(f89,plain,(
% 14.50/2.26    ( ! [X2,X0,X1] : (sK3 != X2 | ~r2_hidden(sK9(X0,X1,X2),sK2) | ~r2_hidden(sK8(X0,X1,X2),sK1) | ~sP7(X2,X1,X0)) )),
% 14.50/2.26    inference(superposition,[],[f25,f47])).
% 14.50/2.26  fof(f47,plain,(
% 14.50/2.26    ( ! [X0,X3,X1] : (k4_tarski(sK8(X0,X1,X3),sK9(X0,X1,X3)) = X3 | ~sP7(X3,X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f14])).
% 14.50/2.26  fof(f25,plain,(
% 14.50/2.26    ( ! [X4,X5] : (k4_tarski(X4,X5) != sK3 | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK1)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f19])).
% 14.50/2.26  fof(f16623,plain,(
% 14.50/2.26    ( ! [X0] : (r1_xboole_0(sK0,k4_xboole_0(X0,k2_zfmisc_1(sK1,sK2)))) )),
% 14.50/2.26    inference(resolution,[],[f2176,f68])).
% 14.50/2.26  fof(f68,plain,(
% 14.50/2.26    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 14.50/2.26    inference(equality_resolution,[],[f35])).
% 14.50/2.26  fof(f35,plain,(
% 14.50/2.26    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 14.50/2.26    inference(cnf_transformation,[],[f4])).
% 14.50/2.26  fof(f4,axiom,(
% 14.50/2.26    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 14.50/2.26  fof(f2176,plain,(
% 14.50/2.26    ( ! [X2,X3] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),X2) | r1_xboole_0(sK0,k4_xboole_0(X3,X2))) )),
% 14.50/2.26    inference(forward_demodulation,[],[f2169,f38])).
% 14.50/2.26  fof(f38,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f10])).
% 14.50/2.26  fof(f10,axiom,(
% 14.50/2.26    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 14.50/2.26  fof(f2169,plain,(
% 14.50/2.26    ( ! [X2,X3] : (r1_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X3,X2),X2)) | ~r1_tarski(k2_zfmisc_1(sK1,sK2),X2)) )),
% 14.50/2.26    inference(superposition,[],[f702,f42])).
% 14.50/2.26  fof(f42,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f1])).
% 14.50/2.26  fof(f1,axiom,(
% 14.50/2.26    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 14.50/2.26  fof(f702,plain,(
% 14.50/2.26    ( ! [X0,X1] : (r1_xboole_0(sK0,k4_xboole_0(k2_xboole_0(X0,X1),X0)) | ~r1_tarski(k2_zfmisc_1(sK1,sK2),X0)) )),
% 14.50/2.26    inference(superposition,[],[f192,f61])).
% 14.50/2.26  fof(f61,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 14.50/2.26    inference(definition_unfolding,[],[f41,f40])).
% 14.50/2.26  fof(f41,plain,(
% 14.50/2.26    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 14.50/2.26    inference(cnf_transformation,[],[f6])).
% 14.50/2.26  fof(f6,axiom,(
% 14.50/2.26    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 14.50/2.26  fof(f192,plain,(
% 14.50/2.26    ( ! [X10,X11] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k4_xboole_0(X11,k4_xboole_0(X11,X10))) | r1_xboole_0(sK0,k4_xboole_0(X10,X11))) )),
% 14.50/2.26    inference(superposition,[],[f108,f62])).
% 14.50/2.26  fof(f108,plain,(
% 14.50/2.26    ( ! [X0,X1] : (~r1_tarski(k2_zfmisc_1(sK1,sK2),k4_xboole_0(X1,X0)) | r1_xboole_0(sK0,X0)) )),
% 14.50/2.26    inference(resolution,[],[f80,f57])).
% 14.50/2.26  fof(f57,plain,(
% 14.50/2.26    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 14.50/2.26    inference(cnf_transformation,[],[f23])).
% 14.50/2.26  fof(f23,plain,(
% 14.50/2.26    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 14.50/2.26    inference(ennf_transformation,[],[f5])).
% 14.50/2.26  fof(f5,axiom,(
% 14.50/2.26    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 14.50/2.26    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 14.50/2.26  fof(f80,plain,(
% 14.50/2.26    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK1,sK2),X0) | r1_xboole_0(sK0,X0)) )),
% 14.50/2.26    inference(resolution,[],[f26,f55])).
% 14.50/2.26  fof(f26,plain,(
% 14.50/2.26    r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 14.50/2.26    inference(cnf_transformation,[],[f19])).
% 14.50/2.26  % SZS output end Proof for theBenchmark
% 14.50/2.26  % (30242)------------------------------
% 14.50/2.26  % (30242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.50/2.26  % (30242)Termination reason: Refutation
% 14.50/2.26  
% 14.50/2.26  % (30242)Memory used [KB]: 8699
% 14.50/2.26  % (30242)Time elapsed: 1.297 s
% 14.50/2.26  % (30242)------------------------------
% 14.50/2.26  % (30242)------------------------------
% 14.50/2.26  % (30206)Success in time 1.869 s
%------------------------------------------------------------------------------
