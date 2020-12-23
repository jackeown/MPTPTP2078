%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  73 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   16
%              Number of atoms          :   91 ( 141 expanded)
%              Number of equality atoms :   44 (  66 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f21,f321])).

fof(f321,plain,(
    ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
    inference(forward_demodulation,[],[f320,f144])).

fof(f144,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f121,f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f121,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k1_xboole_0),X4) ),
    inference(resolution,[],[f103,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f103,plain,(
    ! [X8,X7] : r1_xboole_0(k3_xboole_0(X8,k1_xboole_0),X7) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X8,k1_xboole_0) != k3_xboole_0(X8,k1_xboole_0)
      | r1_xboole_0(k3_xboole_0(X8,k1_xboole_0),X7) ) ),
    inference(superposition,[],[f36,f59])).

fof(f59,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f57,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f29,f22])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f57,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f55,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f55,plain,(
    ! [X3] : k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3)) = k3_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f30,f45])).

fof(f45,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f44])).

fof(f44,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f25,f42])).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k4_xboole_0(X0,X0) = X0 ) ),
    inference(superposition,[],[f32,f22])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) != k3_xboole_0(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(k3_xboole_0(X0,X1),X2) ) ),
    inference(superposition,[],[f25,f29])).

fof(f320,plain,(
    ! [X0] : k8_relset_1(k1_xboole_0,sK0,sK2,X0) = k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f319,f19])).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f319,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | k8_relset_1(k1_xboole_0,sK0,sK2,X0) = k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0) ) ),
    inference(resolution,[],[f119,f20])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k8_relset_1(X1,X2,X0,X3) = k3_xboole_0(k8_relset_1(X1,X2,X0,X3),X1) ) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).

fof(f21,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:14:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (802586624)
% 0.15/0.37  ipcrm: permission denied for id (802652166)
% 0.15/0.37  ipcrm: permission denied for id (802684935)
% 0.15/0.37  ipcrm: permission denied for id (802717704)
% 0.15/0.38  ipcrm: permission denied for id (802750475)
% 0.15/0.39  ipcrm: permission denied for id (802979861)
% 0.15/0.40  ipcrm: permission denied for id (803012636)
% 0.22/0.40  ipcrm: permission denied for id (803045407)
% 0.22/0.40  ipcrm: permission denied for id (803110945)
% 0.22/0.41  ipcrm: permission denied for id (803176484)
% 0.22/0.41  ipcrm: permission denied for id (803242025)
% 0.22/0.42  ipcrm: permission denied for id (803307565)
% 0.22/0.42  ipcrm: permission denied for id (803340334)
% 0.22/0.42  ipcrm: permission denied for id (803373105)
% 0.22/0.43  ipcrm: permission denied for id (803405875)
% 0.22/0.44  ipcrm: permission denied for id (803471418)
% 0.22/0.44  ipcrm: permission denied for id (803569725)
% 0.22/0.44  ipcrm: permission denied for id (803635263)
% 0.22/0.46  ipcrm: permission denied for id (803766347)
% 0.22/0.46  ipcrm: permission denied for id (803799116)
% 0.22/0.46  ipcrm: permission denied for id (803831888)
% 0.22/0.48  ipcrm: permission denied for id (803995746)
% 0.22/0.50  ipcrm: permission denied for id (804126827)
% 0.22/0.51  ipcrm: permission denied for id (804225141)
% 0.22/0.52  ipcrm: permission denied for id (804323451)
% 0.22/0.58  % (2344)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (2348)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.58  % (2351)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.59  % (2346)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.59  % (2344)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f324,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f322])).
% 0.22/0.59  fof(f322,plain,(
% 0.22/0.59    k1_xboole_0 != k1_xboole_0),
% 0.22/0.59    inference(superposition,[],[f21,f321])).
% 0.22/0.59  fof(f321,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,X0)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f320,f144])).
% 0.22/0.59  fof(f144,plain,(
% 0.22/0.59    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(X3,k1_xboole_0)) )),
% 0.22/0.59    inference(superposition,[],[f121,f22])).
% 0.22/0.59  fof(f22,plain,(
% 0.22/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,plain,(
% 0.22/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    inference(rectify,[],[f2])).
% 0.22/0.59  fof(f2,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.59  fof(f121,plain,(
% 0.22/0.59    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k1_xboole_0),X4)) )),
% 0.22/0.59    inference(resolution,[],[f103,f28])).
% 0.22/0.59  fof(f28,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f1,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.59  fof(f103,plain,(
% 0.22/0.59    ( ! [X8,X7] : (r1_xboole_0(k3_xboole_0(X8,k1_xboole_0),X7)) )),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f97])).
% 0.22/0.59  fof(f97,plain,(
% 0.22/0.59    ( ! [X8,X7] : (k3_xboole_0(X8,k1_xboole_0) != k3_xboole_0(X8,k1_xboole_0) | r1_xboole_0(k3_xboole_0(X8,k1_xboole_0),X7)) )),
% 0.22/0.59    inference(superposition,[],[f36,f59])).
% 0.22/0.59  fof(f59,plain,(
% 0.22/0.59    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 0.22/0.59    inference(superposition,[],[f57,f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.59    inference(superposition,[],[f29,f22])).
% 0.22/0.59  fof(f29,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f5])).
% 0.22/0.59  fof(f5,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.22/0.59  fof(f57,plain,(
% 0.22/0.59    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f55,f23])).
% 0.22/0.59  fof(f23,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.59  fof(f55,plain,(
% 0.22/0.59    ( ! [X3] : (k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X3)) = k3_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.59    inference(resolution,[],[f30,f45])).
% 0.22/0.59  fof(f45,plain,(
% 0.22/0.59    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.59    inference(superposition,[],[f25,f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.59    inference(equality_resolution,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 != X0 | k4_xboole_0(X0,X0) = X0) )),
% 0.22/0.59    inference(superposition,[],[f32,f22])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.59    inference(resolution,[],[f27,f26])).
% 0.22/0.59  fof(f26,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f7,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.59  fof(f27,plain,(
% 0.22/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f1])).
% 0.22/0.59  fof(f25,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f7])).
% 0.22/0.59  fof(f30,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f16])).
% 0.22/0.59  fof(f16,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f6])).
% 0.22/0.59  fof(f6,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 0.22/0.59  fof(f36,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) != k3_xboole_0(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.22/0.59    inference(superposition,[],[f25,f29])).
% 0.22/0.59  fof(f320,plain,(
% 0.22/0.59    ( ! [X0] : (k8_relset_1(k1_xboole_0,sK0,sK2,X0) = k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0)) )),
% 0.22/0.59    inference(subsumption_resolution,[],[f319,f19])).
% 0.22/0.59  fof(f19,plain,(
% 0.22/0.59    v1_funct_1(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f13])).
% 0.22/0.59  fof(f13,plain,(
% 0.22/0.59    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f12])).
% 0.22/0.59  fof(f12,plain,(
% 0.22/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.59    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.59  fof(f10,negated_conjecture,(
% 0.22/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.59    inference(negated_conjecture,[],[f9])).
% 0.22/0.59  fof(f9,conjecture,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 0.22/0.59  fof(f319,plain,(
% 0.22/0.59    ( ! [X0] : (~v1_funct_1(sK2) | k8_relset_1(k1_xboole_0,sK0,sK2,X0) = k3_xboole_0(k8_relset_1(k1_xboole_0,sK0,sK2,X0),k1_xboole_0)) )),
% 0.22/0.59    inference(resolution,[],[f119,f20])).
% 0.22/0.59  fof(f20,plain,(
% 0.22/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f119,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k8_relset_1(X1,X2,X0,X3) = k3_xboole_0(k8_relset_1(X1,X2,X0,X3),X1)) )),
% 0.22/0.59    inference(resolution,[],[f31,f24])).
% 0.22/0.59  fof(f24,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,plain,(
% 0.22/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 0.22/0.59    inference(flattening,[],[f17])).
% 0.22/0.59  fof(f17,plain,(
% 0.22/0.59    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.22/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_2)).
% 0.22/0.59  fof(f21,plain,(
% 0.22/0.59    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  % SZS output end Proof for theBenchmark
% 0.22/0.59  % (2344)------------------------------
% 0.22/0.59  % (2344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (2344)Termination reason: Refutation
% 0.22/0.59  
% 0.22/0.59  % (2344)Memory used [KB]: 10746
% 0.22/0.59  % (2344)Time elapsed: 0.013 s
% 0.22/0.59  % (2344)------------------------------
% 0.22/0.59  % (2344)------------------------------
% 0.22/0.59  % (2151)Success in time 0.232 s
%------------------------------------------------------------------------------
