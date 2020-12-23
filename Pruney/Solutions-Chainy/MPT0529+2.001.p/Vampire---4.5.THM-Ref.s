%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:58 EST 2020

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   68 (  96 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   15
%              Number of atoms          :  145 ( 222 expanded)
%              Number of equality atoms :   31 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(subsumption_resolution,[],[f654,f39])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

% (29371)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f35,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).

fof(f654,plain,(
    ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f653,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f76,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (29400)Refutation not found, incomplete strategy% (29400)------------------------------
% (29400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29400)Termination reason: Refutation not found, incomplete strategy

% (29400)Memory used [KB]: 1663
% (29400)Time elapsed: 0.180 s
% (29400)------------------------------
% (29400)------------------------------
fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f653,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f647,f40])).

fof(f40,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f647,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f153,f110])).

fof(f110,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X1) ),
    inference(forward_demodulation,[],[f109,f44])).

fof(f44,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f109,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0),X1) ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f42,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0),X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f83,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f49,f44])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).

fof(f153,plain,(
    ! [X10] :
      ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),X10)
      | ~ r1_tarski(X10,sK1)
      | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ) ),
    inference(resolution,[],[f80,f149])).

fof(f149,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f130,f147])).

fof(f147,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f73,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f48,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f130,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),sK0),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f128,f39])).

fof(f128,plain,
    ( ~ r1_tarski(k3_xboole_0(k2_relat_1(sK2),sK0),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f120,f51])).

fof(f120,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(trivial_inequality_removal,[],[f112])).

fof(f112,plain,
    ( k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2)
    | ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(superposition,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f41,plain,(
    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (29380)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (29377)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (29385)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.56  % (29393)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (29385)Refutation not found, incomplete strategy% (29385)------------------------------
% 0.21/0.56  % (29385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29372)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.56  % (29372)Refutation not found, incomplete strategy% (29372)------------------------------
% 0.21/0.56  % (29372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (29372)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29372)Memory used [KB]: 1663
% 0.21/0.56  % (29372)Time elapsed: 0.140 s
% 0.21/0.56  % (29372)------------------------------
% 0.21/0.56  % (29372)------------------------------
% 1.50/0.57  % (29388)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.50/0.58  % (29374)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.50/0.58  % (29385)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (29385)Memory used [KB]: 1791
% 1.50/0.58  % (29385)Time elapsed: 0.135 s
% 1.50/0.58  % (29385)------------------------------
% 1.50/0.58  % (29385)------------------------------
% 1.80/0.59  % (29376)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.80/0.59  % (29375)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.80/0.59  % (29380)Refutation found. Thanks to Tanya!
% 1.80/0.59  % SZS status Theorem for theBenchmark
% 1.80/0.59  % (29386)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.80/0.60  % (29373)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.80/0.60  % (29394)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.80/0.60  % (29400)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.80/0.60  % SZS output start Proof for theBenchmark
% 1.80/0.60  fof(f657,plain,(
% 1.80/0.60    $false),
% 1.80/0.60    inference(subsumption_resolution,[],[f654,f39])).
% 1.80/0.60  fof(f39,plain,(
% 1.80/0.60    v1_relat_1(sK2)),
% 1.80/0.60    inference(cnf_transformation,[],[f35])).
% 1.80/0.60  % (29371)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.80/0.60  fof(f35,plain,(
% 1.80/0.60    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 1.80/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f34])).
% 1.80/0.60  fof(f34,plain,(
% 1.80/0.60    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 1.80/0.60    introduced(choice_axiom,[])).
% 1.80/0.60  fof(f24,plain,(
% 1.80/0.60    ? [X0,X1,X2] : (k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 1.80/0.60    inference(flattening,[],[f23])).
% 1.80/0.60  fof(f23,plain,(
% 1.80/0.60    ? [X0,X1,X2] : ((k8_relat_1(X0,X2) != k8_relat_1(X1,k8_relat_1(X0,X2)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 1.80/0.60    inference(ennf_transformation,[],[f22])).
% 1.80/0.60  fof(f22,negated_conjecture,(
% 1.80/0.60    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.80/0.60    inference(negated_conjecture,[],[f21])).
% 1.80/0.60  fof(f21,conjecture,(
% 1.80/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_relat_1)).
% 1.80/0.60  fof(f654,plain,(
% 1.80/0.60    ~v1_relat_1(sK2)),
% 1.80/0.60    inference(resolution,[],[f653,f98])).
% 1.80/0.60  fof(f98,plain,(
% 1.80/0.60    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(duplicate_literal_removal,[],[f93])).
% 1.80/0.60  fof(f93,plain,(
% 1.80/0.60    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X1,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(superposition,[],[f76,f50])).
% 1.80/0.60  fof(f50,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f27])).
% 1.80/0.60  fof(f27,plain,(
% 1.80/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f17])).
% 1.80/0.60  fof(f17,axiom,(
% 1.80/0.60    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 1.80/0.60  fof(f76,plain,(
% 1.80/0.60    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,k6_relat_1(X1))) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(duplicate_literal_removal,[],[f75])).
% 1.80/0.60  fof(f75,plain,(
% 1.80/0.60    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k6_relat_1(X1)))) )),
% 1.80/0.60    inference(resolution,[],[f52,f70])).
% 1.80/0.60  fof(f70,plain,(
% 1.80/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~v1_relat_1(X1) | v1_relat_1(X0)) )),
% 1.80/0.60    inference(resolution,[],[f45,f60])).
% 1.80/0.60  fof(f60,plain,(
% 1.80/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f38])).
% 1.80/0.60  fof(f38,plain,(
% 1.80/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.80/0.60    inference(nnf_transformation,[],[f12])).
% 1.80/0.60  fof(f12,axiom,(
% 1.80/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.80/0.60  fof(f45,plain,(
% 1.80/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f25])).
% 1.80/0.60  % (29400)Refutation not found, incomplete strategy% (29400)------------------------------
% 1.80/0.60  % (29400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (29400)Termination reason: Refutation not found, incomplete strategy
% 1.80/0.60  
% 1.80/0.60  % (29400)Memory used [KB]: 1663
% 1.80/0.60  % (29400)Time elapsed: 0.180 s
% 1.80/0.60  % (29400)------------------------------
% 1.80/0.60  % (29400)------------------------------
% 1.80/0.60  fof(f25,plain,(
% 1.80/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.80/0.60    inference(ennf_transformation,[],[f13])).
% 1.80/0.60  fof(f13,axiom,(
% 1.80/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.80/0.60  fof(f52,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f29])).
% 1.80/0.60  fof(f29,plain,(
% 1.80/0.60    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f20])).
% 1.80/0.60  fof(f20,axiom,(
% 1.80/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.80/0.60  fof(f653,plain,(
% 1.80/0.60    ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(subsumption_resolution,[],[f647,f40])).
% 1.80/0.60  fof(f40,plain,(
% 1.80/0.60    r1_tarski(sK0,sK1)),
% 1.80/0.60    inference(cnf_transformation,[],[f35])).
% 1.80/0.60  fof(f647,plain,(
% 1.80/0.60    ~r1_tarski(sK0,sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(resolution,[],[f153,f110])).
% 1.80/0.60  fof(f110,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X1)) )),
% 1.80/0.60    inference(forward_demodulation,[],[f109,f44])).
% 1.80/0.60  fof(f44,plain,(
% 1.80/0.60    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.80/0.60    inference(cnf_transformation,[],[f19])).
% 1.80/0.60  fof(f19,axiom,(
% 1.80/0.60    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.80/0.60  fof(f109,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0),X1)) )),
% 1.80/0.60    inference(subsumption_resolution,[],[f108,f42])).
% 1.80/0.60  fof(f42,plain,(
% 1.80/0.60    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.80/0.60    inference(cnf_transformation,[],[f14])).
% 1.80/0.60  fof(f14,axiom,(
% 1.80/0.60    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.80/0.60  fof(f108,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(k2_relat_1(k6_relat_1(X1)),X0),X1) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.80/0.60    inference(superposition,[],[f83,f51])).
% 1.80/0.60  fof(f51,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f28])).
% 1.80/0.60  fof(f28,plain,(
% 1.80/0.60    ! [X0,X1] : (k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f16])).
% 1.80/0.60  fof(f16,axiom,(
% 1.80/0.60    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k8_relat_1(X0,X1)) = k3_xboole_0(k2_relat_1(X1),X0))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t119_relat_1)).
% 1.80/0.60  fof(f83,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0)) )),
% 1.80/0.60    inference(subsumption_resolution,[],[f82,f42])).
% 1.80/0.60  fof(f82,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X1,k6_relat_1(X0))),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.80/0.60    inference(superposition,[],[f49,f44])).
% 1.80/0.60  fof(f49,plain,(
% 1.80/0.60    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f26])).
% 1.80/0.60  fof(f26,plain,(
% 1.80/0.60    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f15])).
% 1.80/0.60  fof(f15,axiom,(
% 1.80/0.60    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_relat_1)).
% 1.80/0.60  fof(f153,plain,(
% 1.80/0.60    ( ! [X10] : (~r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),X10) | ~r1_tarski(X10,sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))) )),
% 1.80/0.60    inference(resolution,[],[f80,f149])).
% 1.80/0.60  fof(f149,plain,(
% 1.80/0.60    ~r1_tarski(k3_xboole_0(sK0,k2_relat_1(sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(backward_demodulation,[],[f130,f147])).
% 1.80/0.60  fof(f147,plain,(
% 1.80/0.60    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.80/0.60    inference(superposition,[],[f73,f48])).
% 1.80/0.60  fof(f48,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f11])).
% 1.80/0.60  fof(f11,axiom,(
% 1.80/0.60    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.80/0.60  fof(f73,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.80/0.60    inference(superposition,[],[f48,f46])).
% 1.80/0.60  fof(f46,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f4])).
% 1.80/0.60  fof(f4,axiom,(
% 1.80/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.80/0.60  fof(f130,plain,(
% 1.80/0.60    ~r1_tarski(k3_xboole_0(k2_relat_1(sK2),sK0),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(subsumption_resolution,[],[f128,f39])).
% 1.80/0.60  fof(f128,plain,(
% 1.80/0.60    ~r1_tarski(k3_xboole_0(k2_relat_1(sK2),sK0),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(sK2)),
% 1.80/0.60    inference(superposition,[],[f120,f51])).
% 1.80/0.60  fof(f120,plain,(
% 1.80/0.60    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(trivial_inequality_removal,[],[f112])).
% 1.80/0.60  fof(f112,plain,(
% 1.80/0.60    k8_relat_1(sK0,sK2) != k8_relat_1(sK0,sK2) | ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK2)),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(superposition,[],[f41,f54])).
% 1.80/0.60  fof(f54,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f31])).
% 1.80/0.60  fof(f31,plain,(
% 1.80/0.60    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(flattening,[],[f30])).
% 1.80/0.60  fof(f30,plain,(
% 1.80/0.60    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f18])).
% 1.80/0.60  fof(f18,axiom,(
% 1.80/0.60    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 1.80/0.60  fof(f41,plain,(
% 1.80/0.60    k8_relat_1(sK0,sK2) != k8_relat_1(sK1,k8_relat_1(sK0,sK2))),
% 1.80/0.60    inference(cnf_transformation,[],[f35])).
% 1.80/0.60  fof(f80,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.80/0.60    inference(superposition,[],[f62,f55])).
% 1.80/0.60  fof(f55,plain,(
% 1.80/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f32])).
% 1.80/0.60  fof(f32,plain,(
% 1.80/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.80/0.60    inference(ennf_transformation,[],[f3])).
% 1.80/0.60  fof(f3,axiom,(
% 1.80/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.80/0.60  fof(f62,plain,(
% 1.80/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.80/0.60    inference(cnf_transformation,[],[f33])).
% 1.80/0.60  fof(f33,plain,(
% 1.80/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.80/0.60    inference(ennf_transformation,[],[f2])).
% 1.80/0.60  fof(f2,axiom,(
% 1.80/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.80/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.80/0.60  % SZS output end Proof for theBenchmark
% 1.80/0.60  % (29380)------------------------------
% 1.80/0.60  % (29380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.80/0.60  % (29380)Termination reason: Refutation
% 1.80/0.60  
% 1.80/0.60  % (29380)Memory used [KB]: 2174
% 1.80/0.60  % (29380)Time elapsed: 0.178 s
% 1.80/0.60  % (29380)------------------------------
% 1.80/0.60  % (29380)------------------------------
% 1.80/0.60  % (29370)Success in time 0.242 s
%------------------------------------------------------------------------------
