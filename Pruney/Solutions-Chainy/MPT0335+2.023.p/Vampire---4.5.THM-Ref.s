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
% DateTime   : Thu Dec  3 12:43:18 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 345 expanded)
%              Number of leaves         :   14 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  111 ( 887 expanded)
%              Number of equality atoms :   75 ( 508 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f608,plain,(
    $false ),
    inference(subsumption_resolution,[],[f607,f43])).

fof(f43,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k1_tarski(sK3) = k3_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

fof(f607,plain,(
    k3_xboole_0(sK0,sK2) = k1_tarski(sK3) ),
    inference(forward_demodulation,[],[f604,f591])).

fof(f591,plain,(
    k1_tarski(sK3) = k2_xboole_0(k4_xboole_0(k1_tarski(sK3),sK1),k3_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f494,f574])).

fof(f574,plain,(
    k4_xboole_0(k1_tarski(sK3),sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f263,f92])).

fof(f92,plain,(
    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f81,f87])).

fof(f87,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f61,f79])).

fof(f79,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f81,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f68,f77])).

fof(f77,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f263,plain,(
    ! [X0] : k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK3),X0) ),
    inference(forward_demodulation,[],[f250,f164])).

fof(f164,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK3),X0) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0)) ),
    inference(forward_demodulation,[],[f156,f97])).

fof(f97,plain,(
    ! [X4] : k3_xboole_0(sK1,k4_xboole_0(sK2,X4)) = k4_xboole_0(k1_tarski(sK3),X4) ),
    inference(superposition,[],[f59,f41])).

fof(f41,plain,(
    k1_tarski(sK3) = k3_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f156,plain,(
    ! [X0] : k3_xboole_0(sK1,k4_xboole_0(sK2,X0)) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f97,f61])).

fof(f250,plain,(
    ! [X0] : k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0)) ),
    inference(superposition,[],[f99,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK2)) = k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f93,f63])).

fof(f93,plain,(
    ! [X0] : k3_xboole_0(k4_xboole_0(sK1,X0),sK2) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK2)) ),
    inference(superposition,[],[f56,f41])).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).

fof(f494,plain,(
    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f493,f418])).

fof(f418,plain,(
    k3_xboole_0(sK0,sK2) = k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0)) ),
    inference(backward_demodulation,[],[f296,f416])).

fof(f416,plain,(
    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f410,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f410,plain,(
    k3_xboole_0(sK0,k1_tarski(sK3)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f62,f377])).

fof(f377,plain,(
    k4_xboole_0(sK0,k1_tarski(sK3)) = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f367,f90])).

fof(f90,plain,(
    ! [X2] : k3_xboole_0(sK0,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK0,X2) ),
    inference(forward_demodulation,[],[f84,f61])).

fof(f84,plain,(
    ! [X2] : k3_xboole_0(sK0,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK0,k3_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f58,f79])).

fof(f58,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f367,plain,(
    k4_xboole_0(sK0,k1_tarski(sK3)) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f90,f98])).

fof(f98,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_tarski(sK3)) ),
    inference(superposition,[],[f61,f41])).

fof(f296,plain,(
    k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f292,f63])).

fof(f292,plain,(
    k3_xboole_0(k1_tarski(sK3),sK0) = k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0)) ),
    inference(superposition,[],[f62,f102])).

fof(f102,plain,(
    k4_xboole_0(sK0,sK0) = k4_xboole_0(k1_tarski(sK3),sK0) ),
    inference(superposition,[],[f68,f80])).

fof(f80,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK3),sK0) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f42,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f493,plain,(
    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f491,f164])).

fof(f491,plain,(
    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)))) ),
    inference(resolution,[],[f488,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f488,plain,(
    r1_tarski(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k1_tarski(sK3)) ),
    inference(forward_demodulation,[],[f479,f41])).

fof(f479,plain,(
    r1_tarski(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f340,f92])).

fof(f340,plain,(
    ! [X11] : r1_tarski(k3_xboole_0(sK2,k4_xboole_0(X11,sK1)),k3_xboole_0(X11,sK2)) ),
    inference(superposition,[],[f66,f100])).

fof(f100,plain,(
    ! [X1] : k4_xboole_0(k3_xboole_0(X1,sK2),k1_tarski(sK3)) = k3_xboole_0(sK2,k4_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f94,f63])).

fof(f94,plain,(
    ! [X1] : k3_xboole_0(k4_xboole_0(X1,sK1),sK2) = k4_xboole_0(k3_xboole_0(X1,sK2),k1_tarski(sK3)) ),
    inference(superposition,[],[f56,f41])).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f604,plain,(
    k3_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(k1_tarski(sK3),sK1),k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f594,f65])).

fof(f594,plain,(
    r1_tarski(k4_xboole_0(k1_tarski(sK3),sK1),k3_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f478,f574])).

fof(f478,plain,(
    r1_tarski(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f340,f87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (21658)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (21670)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.50  % (21674)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (21662)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (21652)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (21654)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (21666)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (21649)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (21653)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (21648)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (21675)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (21650)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (21672)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (21655)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (21651)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (21676)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (21669)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (21664)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (21664)Refutation not found, incomplete strategy% (21664)------------------------------
% 0.21/0.55  % (21664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (21664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (21664)Memory used [KB]: 10618
% 0.21/0.55  % (21668)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (21664)Time elapsed: 0.136 s
% 0.21/0.55  % (21664)------------------------------
% 0.21/0.55  % (21664)------------------------------
% 0.21/0.55  % (21661)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (21671)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (21665)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (21667)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (21656)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (21677)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (21660)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (21663)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (21659)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (21673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.60/0.57  % (21657)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.60/0.57  % (21666)Refutation found. Thanks to Tanya!
% 1.60/0.57  % SZS status Theorem for theBenchmark
% 1.60/0.57  % SZS output start Proof for theBenchmark
% 1.60/0.57  fof(f608,plain,(
% 1.60/0.57    $false),
% 1.60/0.57    inference(subsumption_resolution,[],[f607,f43])).
% 1.60/0.57  fof(f43,plain,(
% 1.60/0.57    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 1.60/0.57    inference(cnf_transformation,[],[f32])).
% 1.60/0.57  fof(f32,plain,(
% 1.60/0.57    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.60/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).
% 1.60/0.57  fof(f31,plain,(
% 1.60/0.57    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k1_tarski(sK3) = k3_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.60/0.57    introduced(choice_axiom,[])).
% 1.60/0.57  fof(f25,plain,(
% 1.60/0.57    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 1.60/0.57    inference(flattening,[],[f24])).
% 1.60/0.57  fof(f24,plain,(
% 1.60/0.57    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 1.60/0.57    inference(ennf_transformation,[],[f22])).
% 1.60/0.57  fof(f22,negated_conjecture,(
% 1.60/0.57    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 1.60/0.57    inference(negated_conjecture,[],[f21])).
% 1.60/0.57  fof(f21,conjecture,(
% 1.60/0.57    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).
% 1.60/0.57  fof(f607,plain,(
% 1.60/0.57    k3_xboole_0(sK0,sK2) = k1_tarski(sK3)),
% 1.60/0.57    inference(forward_demodulation,[],[f604,f591])).
% 1.60/0.57  fof(f591,plain,(
% 1.60/0.57    k1_tarski(sK3) = k2_xboole_0(k4_xboole_0(k1_tarski(sK3),sK1),k3_xboole_0(sK0,sK2))),
% 1.60/0.57    inference(backward_demodulation,[],[f494,f574])).
% 1.60/0.57  fof(f574,plain,(
% 1.60/0.57    k4_xboole_0(k1_tarski(sK3),sK1) = k3_xboole_0(sK2,k4_xboole_0(sK0,sK0))),
% 1.60/0.57    inference(superposition,[],[f263,f92])).
% 1.60/0.57  fof(f92,plain,(
% 1.60/0.57    k4_xboole_0(sK1,sK1) = k4_xboole_0(sK0,sK0)),
% 1.60/0.57    inference(backward_demodulation,[],[f81,f87])).
% 1.60/0.57  fof(f87,plain,(
% 1.60/0.57    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)),
% 1.60/0.57    inference(superposition,[],[f61,f79])).
% 1.60/0.57  fof(f79,plain,(
% 1.60/0.57    sK0 = k3_xboole_0(sK0,sK1)),
% 1.60/0.57    inference(resolution,[],[f40,f60])).
% 1.60/0.57  fof(f60,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.60/0.57    inference(cnf_transformation,[],[f28])).
% 1.60/0.57  fof(f28,plain,(
% 1.60/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f5])).
% 1.60/0.57  fof(f5,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.60/0.57  fof(f40,plain,(
% 1.60/0.57    r1_tarski(sK0,sK1)),
% 1.60/0.57    inference(cnf_transformation,[],[f32])).
% 1.60/0.57  fof(f61,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f12])).
% 1.60/0.57  fof(f12,axiom,(
% 1.60/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.60/0.57  fof(f81,plain,(
% 1.60/0.57    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK1,sK1)),
% 1.60/0.57    inference(superposition,[],[f68,f77])).
% 1.60/0.57  fof(f77,plain,(
% 1.60/0.57    sK1 = k2_xboole_0(sK0,sK1)),
% 1.60/0.57    inference(resolution,[],[f40,f65])).
% 1.60/0.57  fof(f65,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f30])).
% 1.60/0.57  fof(f30,plain,(
% 1.60/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f4])).
% 1.60/0.57  fof(f4,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.60/0.57  fof(f68,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f9])).
% 1.60/0.57  fof(f9,axiom,(
% 1.60/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.60/0.57  fof(f263,plain,(
% 1.60/0.57    ( ! [X0] : (k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK3),X0)) )),
% 1.60/0.57    inference(forward_demodulation,[],[f250,f164])).
% 1.60/0.57  fof(f164,plain,(
% 1.60/0.57    ( ! [X0] : (k4_xboole_0(k1_tarski(sK3),X0) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0))) )),
% 1.60/0.57    inference(forward_demodulation,[],[f156,f97])).
% 1.60/0.57  fof(f97,plain,(
% 1.60/0.57    ( ! [X4] : (k3_xboole_0(sK1,k4_xboole_0(sK2,X4)) = k4_xboole_0(k1_tarski(sK3),X4)) )),
% 1.60/0.57    inference(superposition,[],[f59,f41])).
% 1.60/0.57  fof(f41,plain,(
% 1.60/0.57    k1_tarski(sK3) = k3_xboole_0(sK1,sK2)),
% 1.60/0.57    inference(cnf_transformation,[],[f32])).
% 1.60/0.57  fof(f59,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f14])).
% 1.60/0.57  fof(f14,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.60/0.57  fof(f156,plain,(
% 1.60/0.57    ( ! [X0] : (k3_xboole_0(sK1,k4_xboole_0(sK2,X0)) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0))) )),
% 1.60/0.57    inference(superposition,[],[f97,f61])).
% 1.60/0.57  fof(f250,plain,(
% 1.60/0.57    ( ! [X0] : (k3_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0))) )),
% 1.60/0.57    inference(superposition,[],[f99,f63])).
% 1.60/0.57  fof(f63,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f1])).
% 1.60/0.57  fof(f1,axiom,(
% 1.60/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.60/0.57  fof(f99,plain,(
% 1.60/0.57    ( ! [X0] : (k4_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK2)) = k3_xboole_0(sK2,k4_xboole_0(sK1,X0))) )),
% 1.60/0.57    inference(forward_demodulation,[],[f93,f63])).
% 1.60/0.57  fof(f93,plain,(
% 1.60/0.57    ( ! [X0] : (k3_xboole_0(k4_xboole_0(sK1,X0),sK2) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK2))) )),
% 1.60/0.57    inference(superposition,[],[f56,f41])).
% 1.60/0.57  fof(f56,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f3])).
% 1.60/0.57  fof(f3,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k4_xboole_0(X0,X2),X1)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_xboole_1)).
% 1.60/0.57  fof(f494,plain,(
% 1.60/0.57    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK2))),
% 1.60/0.57    inference(forward_demodulation,[],[f493,f418])).
% 1.60/0.57  fof(f418,plain,(
% 1.60/0.57    k3_xboole_0(sK0,sK2) = k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0))),
% 1.60/0.57    inference(backward_demodulation,[],[f296,f416])).
% 1.60/0.57  fof(f416,plain,(
% 1.60/0.57    k3_xboole_0(sK0,sK2) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.60/0.57    inference(forward_demodulation,[],[f410,f62])).
% 1.60/0.57  fof(f62,plain,(
% 1.60/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f13])).
% 1.60/0.57  fof(f13,axiom,(
% 1.60/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.60/0.57  fof(f410,plain,(
% 1.60/0.57    k3_xboole_0(sK0,k1_tarski(sK3)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.60/0.57    inference(superposition,[],[f62,f377])).
% 1.60/0.57  fof(f377,plain,(
% 1.60/0.57    k4_xboole_0(sK0,k1_tarski(sK3)) = k4_xboole_0(sK0,sK2)),
% 1.60/0.57    inference(forward_demodulation,[],[f367,f90])).
% 1.60/0.57  fof(f90,plain,(
% 1.60/0.57    ( ! [X2] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK0,X2)) )),
% 1.60/0.57    inference(forward_demodulation,[],[f84,f61])).
% 1.60/0.57  fof(f84,plain,(
% 1.60/0.57    ( ! [X2] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X2)) = k4_xboole_0(sK0,k3_xboole_0(sK0,X2))) )),
% 1.60/0.57    inference(superposition,[],[f58,f79])).
% 1.60/0.57  fof(f58,plain,(
% 1.60/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 1.60/0.57    inference(cnf_transformation,[],[f15])).
% 1.60/0.57  fof(f15,axiom,(
% 1.60/0.57    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 1.60/0.57  fof(f367,plain,(
% 1.60/0.57    k4_xboole_0(sK0,k1_tarski(sK3)) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 1.60/0.57    inference(superposition,[],[f90,f98])).
% 1.60/0.57  fof(f98,plain,(
% 1.60/0.57    k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k1_tarski(sK3))),
% 1.60/0.57    inference(superposition,[],[f61,f41])).
% 1.60/0.57  fof(f296,plain,(
% 1.60/0.57    k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0)) = k3_xboole_0(sK0,k1_tarski(sK3))),
% 1.60/0.57    inference(forward_demodulation,[],[f292,f63])).
% 1.60/0.57  fof(f292,plain,(
% 1.60/0.57    k3_xboole_0(k1_tarski(sK3),sK0) = k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0))),
% 1.60/0.57    inference(superposition,[],[f62,f102])).
% 1.60/0.57  fof(f102,plain,(
% 1.60/0.57    k4_xboole_0(sK0,sK0) = k4_xboole_0(k1_tarski(sK3),sK0)),
% 1.60/0.57    inference(superposition,[],[f68,f80])).
% 1.60/0.57  fof(f80,plain,(
% 1.60/0.57    sK0 = k2_xboole_0(k1_tarski(sK3),sK0)),
% 1.60/0.57    inference(resolution,[],[f42,f53])).
% 1.60/0.57  fof(f53,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f26])).
% 1.60/0.57  fof(f26,plain,(
% 1.60/0.57    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f19])).
% 1.60/0.57  fof(f19,axiom,(
% 1.60/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.60/0.57  fof(f42,plain,(
% 1.60/0.57    r2_hidden(sK3,sK0)),
% 1.60/0.57    inference(cnf_transformation,[],[f32])).
% 1.60/0.57  fof(f493,plain,(
% 1.60/0.57    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k1_tarski(sK3),k4_xboole_0(sK0,sK0)))),
% 1.60/0.57    inference(forward_demodulation,[],[f491,f164])).
% 1.60/0.57  fof(f491,plain,(
% 1.60/0.57    k1_tarski(sK3) = k2_xboole_0(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,k4_xboole_0(sK0,sK0))))),
% 1.60/0.57    inference(resolution,[],[f488,f64])).
% 1.60/0.57  fof(f64,plain,(
% 1.60/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 1.60/0.57    inference(cnf_transformation,[],[f29])).
% 1.60/0.57  fof(f29,plain,(
% 1.60/0.57    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 1.60/0.57    inference(ennf_transformation,[],[f11])).
% 1.60/0.57  fof(f11,axiom,(
% 1.60/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 1.60/0.57  fof(f488,plain,(
% 1.60/0.57    r1_tarski(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k1_tarski(sK3))),
% 1.60/0.57    inference(forward_demodulation,[],[f479,f41])).
% 1.60/0.57  fof(f479,plain,(
% 1.60/0.57    r1_tarski(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k3_xboole_0(sK1,sK2))),
% 1.60/0.57    inference(superposition,[],[f340,f92])).
% 1.60/0.57  fof(f340,plain,(
% 1.60/0.57    ( ! [X11] : (r1_tarski(k3_xboole_0(sK2,k4_xboole_0(X11,sK1)),k3_xboole_0(X11,sK2))) )),
% 1.60/0.57    inference(superposition,[],[f66,f100])).
% 1.60/0.57  fof(f100,plain,(
% 1.60/0.57    ( ! [X1] : (k4_xboole_0(k3_xboole_0(X1,sK2),k1_tarski(sK3)) = k3_xboole_0(sK2,k4_xboole_0(X1,sK1))) )),
% 1.60/0.57    inference(forward_demodulation,[],[f94,f63])).
% 1.60/0.57  fof(f94,plain,(
% 1.60/0.57    ( ! [X1] : (k3_xboole_0(k4_xboole_0(X1,sK1),sK2) = k4_xboole_0(k3_xboole_0(X1,sK2),k1_tarski(sK3))) )),
% 1.60/0.57    inference(superposition,[],[f56,f41])).
% 1.60/0.57  fof(f66,plain,(
% 1.60/0.57    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.60/0.57    inference(cnf_transformation,[],[f7])).
% 1.60/0.57  fof(f7,axiom,(
% 1.60/0.57    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.60/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.60/0.57  fof(f604,plain,(
% 1.60/0.57    k3_xboole_0(sK0,sK2) = k2_xboole_0(k4_xboole_0(k1_tarski(sK3),sK1),k3_xboole_0(sK0,sK2))),
% 1.60/0.57    inference(resolution,[],[f594,f65])).
% 1.60/0.57  fof(f594,plain,(
% 1.60/0.57    r1_tarski(k4_xboole_0(k1_tarski(sK3),sK1),k3_xboole_0(sK0,sK2))),
% 1.60/0.57    inference(backward_demodulation,[],[f478,f574])).
% 1.60/0.57  fof(f478,plain,(
% 1.60/0.57    r1_tarski(k3_xboole_0(sK2,k4_xboole_0(sK0,sK0)),k3_xboole_0(sK0,sK2))),
% 1.60/0.57    inference(superposition,[],[f340,f87])).
% 1.60/0.57  % SZS output end Proof for theBenchmark
% 1.60/0.57  % (21666)------------------------------
% 1.60/0.57  % (21666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.57  % (21666)Termination reason: Refutation
% 1.60/0.57  
% 1.60/0.57  % (21666)Memory used [KB]: 2174
% 1.60/0.57  % (21666)Time elapsed: 0.158 s
% 1.60/0.57  % (21666)------------------------------
% 1.60/0.57  % (21666)------------------------------
% 1.60/0.57  % (21647)Success in time 0.217 s
%------------------------------------------------------------------------------
