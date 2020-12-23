%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:17 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 119 expanded)
%              Number of leaves         :   15 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  133 ( 274 expanded)
%              Number of equality atoms :   63 ( 111 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f605,plain,(
    $false ),
    inference(subsumption_resolution,[],[f593,f223])).

fof(f223,plain,(
    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f47,f134])).

fof(f134,plain,(
    ! [X2,X1] : k10_relat_1(k7_relat_1(sK0,X1),X2) = k3_xboole_0(X1,k10_relat_1(sK0,X2)) ),
    inference(forward_demodulation,[],[f133,f90])).

fof(f90,plain,(
    ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0) ),
    inference(resolution,[],[f60,f44])).

fof(f44,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f133,plain,(
    ! [X2,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k3_xboole_0(X1,k10_relat_1(sK0,X2)) ),
    inference(forward_demodulation,[],[f130,f113])).

fof(f113,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f112,f104])).

fof(f104,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(forward_demodulation,[],[f102,f99])).

fof(f99,plain,(
    ! [X10,X11] : k3_xboole_0(X10,X11) = k2_relat_1(k7_relat_1(k6_relat_1(X10),X11)) ),
    inference(superposition,[],[f53,f93])).

fof(f93,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(backward_demodulation,[],[f57,f91])).

fof(f91,plain,(
    ! [X2,X1] : k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1)) ),
    inference(resolution,[],[f60,f50])).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f57,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f53,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f102,plain,(
    ! [X2,X1] : k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2) ),
    inference(resolution,[],[f61,f50])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f112,plain,(
    ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f111,f49])).

fof(f49,plain,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

fof(f111,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) ),
    inference(subsumption_resolution,[],[f110,f50])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f109,f51])).

fof(f51,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f65,f48])).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f130,plain,(
    ! [X2,X1] : k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2)) ),
    inference(resolution,[],[f116,f50])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(k5_relat_1(X0,sK0),X1) = k10_relat_1(X0,k10_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f63,f44])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).

fof(f47,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f593,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f230,f170])).

fof(f170,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f79,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f56,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f230,plain,(
    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f225,f53])).

fof(f225,plain,(
    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2))) ),
    inference(superposition,[],[f99,f186])).

fof(f186,plain,(
    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1) ),
    inference(resolution,[],[f108,f46])).

fof(f46,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f106,f52])).

fof(f52,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k1_relat_1(k6_relat_1(X1)),X2)
      | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2) ) ),
    inference(resolution,[],[f62,f50])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (3867)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (3859)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (3849)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (3847)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (3845)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (3851)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (3856)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (3846)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (3855)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (3872)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (3860)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (3848)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  % (3866)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (3850)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (3862)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (3857)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (3854)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (3855)Refutation not found, incomplete strategy% (3855)------------------------------
% 0.22/0.53  % (3855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3869)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (3855)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3855)Memory used [KB]: 10746
% 0.22/0.54  % (3855)Time elapsed: 0.133 s
% 0.22/0.54  % (3855)------------------------------
% 0.22/0.54  % (3855)------------------------------
% 0.22/0.54  % (3865)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.54  % (3863)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (3853)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.55  % (3852)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.55  % (3864)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.55  % (3868)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.55  % (3861)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.55  % (3861)Refutation not found, incomplete strategy% (3861)------------------------------
% 1.44/0.55  % (3861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (3871)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.55  % (3861)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (3861)Memory used [KB]: 10618
% 1.44/0.55  % (3861)Time elapsed: 0.138 s
% 1.44/0.55  % (3861)------------------------------
% 1.44/0.55  % (3861)------------------------------
% 1.44/0.55  % (3858)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.44/0.55  % (3873)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.44/0.56  % (3873)Refutation not found, incomplete strategy% (3873)------------------------------
% 1.44/0.56  % (3873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (3873)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (3873)Memory used [KB]: 10746
% 1.44/0.56  % (3873)Time elapsed: 0.151 s
% 1.44/0.56  % (3873)------------------------------
% 1.44/0.56  % (3873)------------------------------
% 1.44/0.56  % (3870)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.56  % (3874)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.58/0.56  % (3874)Refutation not found, incomplete strategy% (3874)------------------------------
% 1.58/0.56  % (3874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (3874)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (3874)Memory used [KB]: 1663
% 1.58/0.56  % (3874)Time elapsed: 0.145 s
% 1.58/0.56  % (3874)------------------------------
% 1.58/0.56  % (3874)------------------------------
% 1.58/0.58  % (3852)Refutation found. Thanks to Tanya!
% 1.58/0.58  % SZS status Theorem for theBenchmark
% 1.58/0.58  % SZS output start Proof for theBenchmark
% 1.58/0.58  fof(f605,plain,(
% 1.58/0.58    $false),
% 1.58/0.58    inference(subsumption_resolution,[],[f593,f223])).
% 1.58/0.58  fof(f223,plain,(
% 1.58/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.58/0.58    inference(superposition,[],[f47,f134])).
% 1.58/0.58  fof(f134,plain,(
% 1.58/0.58    ( ! [X2,X1] : (k10_relat_1(k7_relat_1(sK0,X1),X2) = k3_xboole_0(X1,k10_relat_1(sK0,X2))) )),
% 1.58/0.58    inference(forward_demodulation,[],[f133,f90])).
% 1.58/0.58  fof(f90,plain,(
% 1.58/0.58    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) )),
% 1.58/0.58    inference(resolution,[],[f60,f44])).
% 1.58/0.58  fof(f44,plain,(
% 1.58/0.58    v1_relat_1(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f41])).
% 1.58/0.58  fof(f41,plain,(
% 1.58/0.58    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f40,f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f40,plain,(
% 1.58/0.58    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f27,plain,(
% 1.58/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.58/0.58    inference(flattening,[],[f26])).
% 1.58/0.58  fof(f26,plain,(
% 1.58/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f25])).
% 1.58/0.58  fof(f25,negated_conjecture,(
% 1.58/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.58/0.58    inference(negated_conjecture,[],[f24])).
% 1.58/0.58  fof(f24,conjecture,(
% 1.58/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.58/0.60  fof(f60,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f30])).
% 1.58/0.60  fof(f30,plain,(
% 1.58/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.58/0.60    inference(ennf_transformation,[],[f17])).
% 1.58/0.60  fof(f17,axiom,(
% 1.58/0.60    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.58/0.60  fof(f133,plain,(
% 1.58/0.60    ( ! [X2,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k3_xboole_0(X1,k10_relat_1(sK0,X2))) )),
% 1.58/0.60    inference(forward_demodulation,[],[f130,f113])).
% 1.58/0.60  fof(f113,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.58/0.60    inference(forward_demodulation,[],[f112,f104])).
% 1.58/0.60  fof(f104,plain,(
% 1.58/0.60    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.58/0.60    inference(forward_demodulation,[],[f102,f99])).
% 1.58/0.60  fof(f99,plain,(
% 1.58/0.60    ( ! [X10,X11] : (k3_xboole_0(X10,X11) = k2_relat_1(k7_relat_1(k6_relat_1(X10),X11))) )),
% 1.58/0.60    inference(superposition,[],[f53,f93])).
% 1.58/0.60  fof(f93,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 1.58/0.60    inference(backward_demodulation,[],[f57,f91])).
% 1.58/0.60  fof(f91,plain,(
% 1.58/0.60    ( ! [X2,X1] : (k7_relat_1(k6_relat_1(X1),X2) = k5_relat_1(k6_relat_1(X2),k6_relat_1(X1))) )),
% 1.58/0.60    inference(resolution,[],[f60,f50])).
% 1.58/0.60  fof(f50,plain,(
% 1.58/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f19])).
% 1.58/0.60  fof(f19,axiom,(
% 1.58/0.60    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.58/0.60  fof(f57,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f21])).
% 1.58/0.60  fof(f21,axiom,(
% 1.58/0.60    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.58/0.60  fof(f53,plain,(
% 1.58/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.58/0.60    inference(cnf_transformation,[],[f15])).
% 1.58/0.60  fof(f15,axiom,(
% 1.58/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.58/0.60  fof(f102,plain,(
% 1.58/0.60    ( ! [X2,X1] : (k2_relat_1(k7_relat_1(k6_relat_1(X1),X2)) = k9_relat_1(k6_relat_1(X1),X2)) )),
% 1.58/0.60    inference(resolution,[],[f61,f50])).
% 1.58/0.60  fof(f61,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f31])).
% 1.58/0.60  fof(f31,plain,(
% 1.58/0.60    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.58/0.60    inference(ennf_transformation,[],[f13])).
% 1.58/0.60  fof(f13,axiom,(
% 1.58/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.58/0.60  fof(f112,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.58/0.60    inference(forward_demodulation,[],[f111,f49])).
% 1.58/0.60  fof(f49,plain,(
% 1.58/0.60    ( ! [X0] : (k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f23])).
% 1.58/0.60  fof(f23,axiom,(
% 1.58/0.60    ! [X0] : k6_relat_1(X0) = k2_funct_1(k6_relat_1(X0))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).
% 1.58/0.60  fof(f111,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1)) )),
% 1.58/0.60    inference(subsumption_resolution,[],[f110,f50])).
% 1.58/0.60  fof(f110,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.58/0.60    inference(subsumption_resolution,[],[f109,f51])).
% 1.58/0.60  fof(f51,plain,(
% 1.58/0.60    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f19])).
% 1.58/0.60  fof(f109,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k9_relat_1(k2_funct_1(k6_relat_1(X0)),X1) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.58/0.60    inference(resolution,[],[f65,f48])).
% 1.58/0.60  fof(f48,plain,(
% 1.58/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.58/0.60    inference(cnf_transformation,[],[f22])).
% 1.58/0.60  fof(f22,axiom,(
% 1.58/0.60    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.58/0.60  fof(f65,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f37])).
% 1.58/0.60  fof(f37,plain,(
% 1.58/0.60    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.60    inference(flattening,[],[f36])).
% 1.58/0.60  fof(f36,plain,(
% 1.58/0.60    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.60    inference(ennf_transformation,[],[f20])).
% 1.58/0.60  fof(f20,axiom,(
% 1.58/0.60    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.58/0.60  fof(f130,plain,(
% 1.58/0.60    ( ! [X2,X1] : (k10_relat_1(k5_relat_1(k6_relat_1(X1),sK0),X2) = k10_relat_1(k6_relat_1(X1),k10_relat_1(sK0,X2))) )),
% 1.58/0.60    inference(resolution,[],[f116,f50])).
% 1.58/0.60  fof(f116,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | k10_relat_1(k5_relat_1(X0,sK0),X1) = k10_relat_1(X0,k10_relat_1(sK0,X1))) )),
% 1.58/0.60    inference(resolution,[],[f63,f44])).
% 1.58/0.60  fof(f63,plain,(
% 1.58/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f34])).
% 1.58/0.60  fof(f34,plain,(
% 1.58/0.60    ! [X0,X1] : (! [X2] : (k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.58/0.60    inference(ennf_transformation,[],[f14])).
% 1.58/0.60  fof(f14,axiom,(
% 1.58/0.60    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k10_relat_1(k5_relat_1(X1,X2),X0) = k10_relat_1(X1,k10_relat_1(X2,X0))))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t181_relat_1)).
% 1.58/0.60  fof(f47,plain,(
% 1.58/0.60    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.58/0.60    inference(cnf_transformation,[],[f41])).
% 1.58/0.60  fof(f593,plain,(
% 1.58/0.60    k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.58/0.60    inference(superposition,[],[f230,f170])).
% 1.58/0.60  fof(f170,plain,(
% 1.58/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.58/0.60    inference(superposition,[],[f79,f56])).
% 1.58/0.60  fof(f56,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f11])).
% 1.58/0.60  fof(f11,axiom,(
% 1.58/0.60    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.58/0.60  fof(f79,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.58/0.60    inference(superposition,[],[f56,f54])).
% 1.58/0.60  fof(f54,plain,(
% 1.58/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.58/0.60    inference(cnf_transformation,[],[f4])).
% 1.58/0.60  fof(f4,axiom,(
% 1.58/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.58/0.60  fof(f230,plain,(
% 1.58/0.60    k10_relat_1(sK0,sK2) = k3_xboole_0(k10_relat_1(sK0,sK2),sK1)),
% 1.58/0.60    inference(forward_demodulation,[],[f225,f53])).
% 1.58/0.60  fof(f225,plain,(
% 1.58/0.60    k3_xboole_0(k10_relat_1(sK0,sK2),sK1) = k2_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)))),
% 1.58/0.60    inference(superposition,[],[f99,f186])).
% 1.58/0.60  fof(f186,plain,(
% 1.58/0.60    k6_relat_1(k10_relat_1(sK0,sK2)) = k7_relat_1(k6_relat_1(k10_relat_1(sK0,sK2)),sK1)),
% 1.58/0.60    inference(resolution,[],[f108,f46])).
% 1.58/0.60  fof(f46,plain,(
% 1.58/0.60    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.58/0.60    inference(cnf_transformation,[],[f41])).
% 1.58/0.60  fof(f108,plain,(
% 1.58/0.60    ( ! [X2,X1] : (~r1_tarski(X1,X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.58/0.60    inference(forward_demodulation,[],[f106,f52])).
% 1.58/0.60  fof(f52,plain,(
% 1.58/0.60    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.58/0.60    inference(cnf_transformation,[],[f15])).
% 1.58/0.60  fof(f106,plain,(
% 1.58/0.60    ( ! [X2,X1] : (~r1_tarski(k1_relat_1(k6_relat_1(X1)),X2) | k6_relat_1(X1) = k7_relat_1(k6_relat_1(X1),X2)) )),
% 1.58/0.60    inference(resolution,[],[f62,f50])).
% 1.58/0.60  fof(f62,plain,(
% 1.58/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) = X1) )),
% 1.58/0.60    inference(cnf_transformation,[],[f33])).
% 1.58/0.60  fof(f33,plain,(
% 1.58/0.60    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.58/0.60    inference(flattening,[],[f32])).
% 1.58/0.60  fof(f32,plain,(
% 1.58/0.60    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.58/0.60    inference(ennf_transformation,[],[f18])).
% 1.58/0.60  fof(f18,axiom,(
% 1.58/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 1.58/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).
% 1.58/0.60  % SZS output end Proof for theBenchmark
% 1.58/0.60  % (3852)------------------------------
% 1.58/0.60  % (3852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.60  % (3852)Termination reason: Refutation
% 1.58/0.60  
% 1.58/0.60  % (3852)Memory used [KB]: 2302
% 1.58/0.60  % (3852)Time elapsed: 0.170 s
% 1.58/0.60  % (3852)------------------------------
% 1.58/0.60  % (3852)------------------------------
% 1.58/0.60  % (3844)Success in time 0.242 s
%------------------------------------------------------------------------------
