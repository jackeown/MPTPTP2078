%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:24 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 255 expanded)
%              Number of leaves         :   12 (  74 expanded)
%              Depth                    :   14
%              Number of atoms          :  136 ( 502 expanded)
%              Number of equality atoms :   66 ( 237 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f827,plain,(
    $false ),
    inference(subsumption_resolution,[],[f818,f113])).

fof(f113,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f42,f92])).

fof(f92,plain,(
    ! [X0,X1] : k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1)) ),
    inference(resolution,[],[f61,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

fof(f42,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f818,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f328,f220])).

fof(f220,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f216,f45])).

fof(f45,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f216,plain,(
    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f83,f176])).

fof(f176,plain,(
    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f91,f41])).

fof(f41,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f90,f45])).

fof(f90,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f83,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f45,f79])).

fof(f79,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f52,f78])).

fof(f78,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f52,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f328,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k3_xboole_0(X2,k3_xboole_0(X3,X2)) ),
    inference(backward_demodulation,[],[f301,f305])).

fof(f305,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k3_xboole_0(X5,X4) ),
    inference(forward_demodulation,[],[f296,f301])).

fof(f296,plain,(
    ! [X4,X5] : k10_relat_1(k6_relat_1(X4),X5) = k3_xboole_0(X4,k10_relat_1(k6_relat_1(X4),X5)) ),
    inference(superposition,[],[f93,f171])).

fof(f171,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f91,f64])).

fof(f64,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f93,plain,(
    ! [X4,X2,X3] : k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k3_xboole_0(X3,k10_relat_1(k6_relat_1(X2),X4)) ),
    inference(resolution,[],[f61,f43])).

fof(f301,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) = k3_xboole_0(X3,X2) ),
    inference(backward_demodulation,[],[f191,f300])).

fof(f300,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f292,f46])).

fof(f46,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f292,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f82,f171])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f46,f79])).

fof(f191,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f99,f88])).

fof(f88,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(forward_demodulation,[],[f87,f82])).

fof(f87,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f99,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f98,f45])).

fof(f98,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k3_xboole_0(X1,k1_relat_1(k6_relat_1(X1)))) ),
    inference(forward_demodulation,[],[f97,f88])).

fof(f97,plain,(
    ! [X2,X1] : k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) ),
    inference(subsumption_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X2,X1] :
      ( k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f57,f44])).

fof(f44,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (3799)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (3807)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (3791)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (3789)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3790)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3788)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (3798)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (3785)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (3785)Refutation not found, incomplete strategy% (3785)------------------------------
% 0.21/0.52  % (3785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3785)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3785)Memory used [KB]: 1663
% 0.21/0.52  % (3785)Time elapsed: 0.104 s
% 0.21/0.52  % (3785)------------------------------
% 0.21/0.52  % (3785)------------------------------
% 0.21/0.52  % (3805)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (3804)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (3784)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (3796)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (3797)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (3813)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (3811)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (3800)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (3810)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (3793)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (3787)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (3786)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (3812)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (3803)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (3802)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (3792)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (3806)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.55  % (3795)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (3794)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (3801)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (3809)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (3810)Refutation not found, incomplete strategy% (3810)------------------------------
% 0.21/0.56  % (3810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3810)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3810)Memory used [KB]: 6268
% 0.21/0.56  % (3810)Time elapsed: 0.148 s
% 0.21/0.56  % (3810)------------------------------
% 0.21/0.56  % (3810)------------------------------
% 0.21/0.56  % (3808)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.64/0.58  % (3791)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.58  % SZS output start Proof for theBenchmark
% 1.64/0.58  fof(f827,plain,(
% 1.64/0.58    $false),
% 1.64/0.58    inference(subsumption_resolution,[],[f818,f113])).
% 1.64/0.58  fof(f113,plain,(
% 1.64/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.64/0.58    inference(superposition,[],[f42,f92])).
% 1.64/0.58  fof(f92,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k10_relat_1(k7_relat_1(sK0,X0),X1) = k3_xboole_0(X0,k10_relat_1(sK0,X1))) )),
% 1.64/0.58    inference(resolution,[],[f61,f39])).
% 1.64/0.58  fof(f39,plain,(
% 1.64/0.58    v1_relat_1(sK0)),
% 1.64/0.58    inference(cnf_transformation,[],[f36])).
% 1.64/0.58  fof(f36,plain,(
% 1.64/0.58    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.64/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f35,f34])).
% 1.64/0.58  fof(f34,plain,(
% 1.64/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f35,plain,(
% 1.64/0.58    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.64/0.58    introduced(choice_axiom,[])).
% 1.64/0.58  fof(f21,plain,(
% 1.64/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.64/0.58    inference(flattening,[],[f20])).
% 1.64/0.58  fof(f20,plain,(
% 1.64/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.64/0.58    inference(ennf_transformation,[],[f19])).
% 1.64/0.58  fof(f19,negated_conjecture,(
% 1.64/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.64/0.58    inference(negated_conjecture,[],[f18])).
% 1.64/0.58  fof(f18,conjecture,(
% 1.64/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).
% 1.64/0.58  fof(f61,plain,(
% 1.64/0.58    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f29])).
% 1.64/0.58  fof(f29,plain,(
% 1.64/0.58    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.64/0.58    inference(ennf_transformation,[],[f14])).
% 1.64/0.58  fof(f14,axiom,(
% 1.64/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).
% 1.64/0.58  fof(f42,plain,(
% 1.64/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.64/0.58    inference(cnf_transformation,[],[f36])).
% 1.64/0.58  fof(f818,plain,(
% 1.64/0.58    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.64/0.58    inference(superposition,[],[f328,f220])).
% 1.64/0.58  fof(f220,plain,(
% 1.64/0.58    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 1.64/0.58    inference(forward_demodulation,[],[f216,f45])).
% 1.64/0.58  fof(f45,plain,(
% 1.64/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f10])).
% 1.64/0.58  fof(f10,axiom,(
% 1.64/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.64/0.58  fof(f216,plain,(
% 1.64/0.58    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k1_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.64/0.58    inference(superposition,[],[f83,f176])).
% 1.64/0.58  fof(f176,plain,(
% 1.64/0.58    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.64/0.58    inference(resolution,[],[f91,f41])).
% 1.64/0.58  fof(f41,plain,(
% 1.64/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.64/0.58    inference(cnf_transformation,[],[f36])).
% 1.64/0.58  fof(f91,plain,(
% 1.64/0.58    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f90,f45])).
% 1.64/0.58  fof(f90,plain,(
% 1.64/0.58    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.64/0.58    inference(resolution,[],[f56,f43])).
% 1.64/0.58  fof(f43,plain,(
% 1.64/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f13])).
% 1.64/0.58  fof(f13,axiom,(
% 1.64/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.64/0.58  fof(f56,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f26])).
% 1.64/0.58  fof(f26,plain,(
% 1.64/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(flattening,[],[f25])).
% 1.64/0.58  fof(f25,plain,(
% 1.64/0.58    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f12])).
% 1.64/0.58  fof(f12,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 1.64/0.58  fof(f83,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k1_relat_1(k7_relat_1(k6_relat_1(X2),X3))) )),
% 1.64/0.58    inference(superposition,[],[f45,f79])).
% 1.64/0.58  fof(f79,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.64/0.58    inference(backward_demodulation,[],[f52,f78])).
% 1.64/0.58  fof(f78,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.64/0.58    inference(resolution,[],[f54,f43])).
% 1.64/0.58  fof(f54,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f23])).
% 1.64/0.58  fof(f23,plain,(
% 1.64/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f11])).
% 1.64/0.58  fof(f11,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 1.64/0.58  fof(f52,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f17])).
% 1.64/0.58  fof(f17,axiom,(
% 1.64/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 1.64/0.58  fof(f328,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k3_xboole_0(X2,k3_xboole_0(X3,X2))) )),
% 1.64/0.58    inference(backward_demodulation,[],[f301,f305])).
% 1.64/0.58  fof(f305,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k3_xboole_0(X5,X4)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f296,f301])).
% 1.64/0.58  fof(f296,plain,(
% 1.64/0.58    ( ! [X4,X5] : (k10_relat_1(k6_relat_1(X4),X5) = k3_xboole_0(X4,k10_relat_1(k6_relat_1(X4),X5))) )),
% 1.64/0.58    inference(superposition,[],[f93,f171])).
% 1.64/0.58  fof(f171,plain,(
% 1.64/0.58    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.64/0.58    inference(resolution,[],[f91,f64])).
% 1.64/0.58  fof(f64,plain,(
% 1.64/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.64/0.58    inference(equality_resolution,[],[f59])).
% 1.64/0.58  fof(f59,plain,(
% 1.64/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.64/0.58    inference(cnf_transformation,[],[f38])).
% 1.64/0.58  fof(f38,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(flattening,[],[f37])).
% 1.64/0.58  fof(f37,plain,(
% 1.64/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.64/0.58    inference(nnf_transformation,[],[f1])).
% 1.64/0.58  fof(f1,axiom,(
% 1.64/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.58  fof(f93,plain,(
% 1.64/0.58    ( ! [X4,X2,X3] : (k10_relat_1(k7_relat_1(k6_relat_1(X2),X3),X4) = k3_xboole_0(X3,k10_relat_1(k6_relat_1(X2),X4))) )),
% 1.64/0.58    inference(resolution,[],[f61,f43])).
% 1.64/0.58  fof(f301,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) = k3_xboole_0(X3,X2)) )),
% 1.64/0.58    inference(backward_demodulation,[],[f191,f300])).
% 1.64/0.58  fof(f300,plain,(
% 1.64/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.64/0.58    inference(forward_demodulation,[],[f292,f46])).
% 1.64/0.58  fof(f46,plain,(
% 1.64/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.64/0.58    inference(cnf_transformation,[],[f10])).
% 1.64/0.58  fof(f292,plain,(
% 1.64/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k3_xboole_0(X0,X0)) )),
% 1.64/0.58    inference(superposition,[],[f82,f171])).
% 1.64/0.58  fof(f82,plain,(
% 1.64/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 1.64/0.58    inference(superposition,[],[f46,f79])).
% 1.64/0.58  fof(f191,plain,(
% 1.64/0.58    ( ! [X2,X3] : (k3_xboole_0(X2,k10_relat_1(k6_relat_1(X2),X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X2))) )),
% 1.64/0.58    inference(superposition,[],[f99,f88])).
% 1.64/0.58  fof(f88,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.64/0.58    inference(forward_demodulation,[],[f87,f82])).
% 1.64/0.58  fof(f87,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.64/0.58    inference(resolution,[],[f55,f43])).
% 1.64/0.58  fof(f55,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f24])).
% 1.64/0.58  fof(f24,plain,(
% 1.64/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(ennf_transformation,[],[f8])).
% 1.64/0.58  fof(f8,axiom,(
% 1.64/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.64/0.58  fof(f99,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k3_xboole_0(X1,X1))) )),
% 1.64/0.58    inference(forward_demodulation,[],[f98,f45])).
% 1.64/0.58  fof(f98,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k3_xboole_0(X1,k1_relat_1(k6_relat_1(X1))))) )),
% 1.64/0.58    inference(forward_demodulation,[],[f97,f88])).
% 1.64/0.58  fof(f97,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1))))) )),
% 1.64/0.58    inference(subsumption_resolution,[],[f95,f43])).
% 1.64/0.58  fof(f95,plain,(
% 1.64/0.58    ( ! [X2,X1] : (k9_relat_1(k6_relat_1(X1),k10_relat_1(k6_relat_1(X1),X2)) = k3_xboole_0(X2,k9_relat_1(k6_relat_1(X1),k1_relat_1(k6_relat_1(X1)))) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.64/0.58    inference(resolution,[],[f57,f44])).
% 1.64/0.58  fof(f44,plain,(
% 1.64/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.64/0.58    inference(cnf_transformation,[],[f13])).
% 1.64/0.58  fof(f57,plain,(
% 1.64/0.58    ( ! [X0,X1] : (~v1_funct_1(X1) | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 1.64/0.58    inference(cnf_transformation,[],[f28])).
% 1.64/0.58  fof(f28,plain,(
% 1.64/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.64/0.58    inference(flattening,[],[f27])).
% 1.64/0.58  fof(f27,plain,(
% 1.64/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.64/0.58    inference(ennf_transformation,[],[f15])).
% 1.64/0.58  fof(f15,axiom,(
% 1.64/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.64/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).
% 1.64/0.58  % SZS output end Proof for theBenchmark
% 1.64/0.58  % (3791)------------------------------
% 1.64/0.58  % (3791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (3791)Termination reason: Refutation
% 1.64/0.58  
% 1.64/0.58  % (3791)Memory used [KB]: 2558
% 1.64/0.58  % (3791)Time elapsed: 0.135 s
% 1.64/0.58  % (3791)------------------------------
% 1.64/0.58  % (3791)------------------------------
% 1.64/0.58  % (3783)Success in time 0.217 s
%------------------------------------------------------------------------------
