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
% DateTime   : Thu Dec  3 12:47:49 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 307 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  204 ( 468 expanded)
%              Number of equality atoms :   99 ( 309 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f540,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f37,f157,f538])).

fof(f538,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f537,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f537,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f528,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f528,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f527,f70])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f52,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f527,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f526,f131])).

fof(f131,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f130,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f130,plain,(
    ! [X2,X3] : k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(X2,X2),X3) ),
    inference(forward_demodulation,[],[f125,f44])).

fof(f125,plain,(
    ! [X2,X3] : k2_zfmisc_1(k5_xboole_0(X2,X2),X3) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,X3)) ),
    inference(superposition,[],[f80,f71])).

fof(f71,plain,(
    ! [X0] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f66])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f45,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

% (4969)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X2)) ),
    inference(backward_demodulation,[],[f74,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X2) ),
    inference(definition_unfolding,[],[f62,f67,f67])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f74,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) ),
    inference(definition_unfolding,[],[f60,f68,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f54,f67])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f526,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f525,f40])).

fof(f40,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f525,plain,(
    ! [X0] :
      ( k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f521,f42])).

% (4978)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f521,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k5_relat_1(k1_xboole_0,X0)))))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f96,f41])).

fof(f41,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k5_relat_1(X0,X1) = k1_setfam_1(k3_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f95,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) = k1_setfam_1(k3_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1)))))
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f72,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f72,plain,(
    ! [X0] :
      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f67])).

fof(f48,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f157,plain,(
    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[],[f38,f138])).

fof(f138,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f122,f47])).

fof(f122,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f120,f37])).

fof(f120,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f116,f55])).

fof(f116,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f115,f70])).

fof(f115,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k3_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f102,f112])).

fof(f112,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f111,f44])).

fof(f111,plain,(
    ! [X2,X3] : k1_xboole_0 = k2_zfmisc_1(X3,k5_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f109,f44])).

fof(f109,plain,(
    ! [X2,X3] : k2_zfmisc_1(X3,k5_xboole_0(X2,X2)) = k5_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X3,X2)) ),
    inference(superposition,[],[f79,f71])).

fof(f79,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) ),
    inference(backward_demodulation,[],[f73,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f63,f67,f67])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) ),
    inference(definition_unfolding,[],[f61,f68,f68])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f102,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k3_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))
    | ~ v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f72,f97])).

fof(f97,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f93,f37])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f88,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

% (4967)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f88,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f87,f39])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[],[f86,f47])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f49,f41])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f38,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

% (4974)Refutation not found, incomplete strategy% (4974)------------------------------
% (4974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (4974)Termination reason: Refutation not found, incomplete strategy

% (4974)Memory used [KB]: 10618
% (4974)Time elapsed: 0.148 s
% (4974)------------------------------
% (4974)------------------------------
fof(f22,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (4964)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (4980)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.24/0.52  % (4963)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.52  % (4972)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.24/0.53  % (4958)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.54  % (4961)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (4960)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (4987)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.54  % (4970)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.32/0.54  % (4987)Refutation not found, incomplete strategy% (4987)------------------------------
% 1.32/0.54  % (4987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (4987)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (4987)Memory used [KB]: 1663
% 1.32/0.54  % (4987)Time elapsed: 0.001 s
% 1.32/0.54  % (4987)------------------------------
% 1.32/0.54  % (4987)------------------------------
% 1.32/0.54  % (4974)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.55  % (4976)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.55  % (4982)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.55  % (4977)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (4962)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.55  % (4979)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.55  % (4959)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.55  % (4985)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.56  % (4966)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.56  % (4968)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.56  % (4968)Refutation not found, incomplete strategy% (4968)------------------------------
% 1.32/0.56  % (4968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (4968)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (4968)Memory used [KB]: 10746
% 1.32/0.56  % (4968)Time elapsed: 0.137 s
% 1.32/0.56  % (4968)------------------------------
% 1.32/0.56  % (4968)------------------------------
% 1.32/0.56  % (4986)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.56  % (4984)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (4980)Refutation found. Thanks to Tanya!
% 1.32/0.56  % SZS status Theorem for theBenchmark
% 1.32/0.56  % (4971)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.56  % (4986)Refutation not found, incomplete strategy% (4986)------------------------------
% 1.32/0.56  % (4986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (4986)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (4986)Memory used [KB]: 10746
% 1.32/0.56  % (4986)Time elapsed: 0.139 s
% 1.32/0.56  % (4986)------------------------------
% 1.32/0.56  % (4986)------------------------------
% 1.32/0.56  % SZS output start Proof for theBenchmark
% 1.32/0.56  fof(f540,plain,(
% 1.32/0.56    $false),
% 1.32/0.56    inference(unit_resulting_resolution,[],[f37,f157,f538])).
% 1.32/0.56  fof(f538,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f537,f39])).
% 1.32/0.56  fof(f39,plain,(
% 1.32/0.56    v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    inference(cnf_transformation,[],[f1])).
% 1.32/0.56  fof(f1,axiom,(
% 1.32/0.56    v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.32/0.56  fof(f537,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.32/0.56    inference(resolution,[],[f528,f47])).
% 1.32/0.56  fof(f47,plain,(
% 1.32/0.56    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f25])).
% 1.32/0.56  fof(f25,plain,(
% 1.32/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f15])).
% 1.32/0.56  fof(f15,axiom,(
% 1.32/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.32/0.56  fof(f528,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f527,f70])).
% 1.32/0.56  fof(f70,plain,(
% 1.32/0.56    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k1_xboole_0))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f43,f67])).
% 1.32/0.56  fof(f67,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f52,f66])).
% 1.32/0.56  fof(f66,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f53,f65])).
% 1.32/0.56  fof(f65,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f59,f64])).
% 1.32/0.56  fof(f64,plain,(
% 1.32/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f10])).
% 1.32/0.56  fof(f10,axiom,(
% 1.32/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.56  fof(f59,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f9])).
% 1.32/0.56  fof(f9,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.56  fof(f53,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f8])).
% 1.32/0.56  fof(f8,axiom,(
% 1.32/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.56  fof(f52,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f14])).
% 1.32/0.56  fof(f14,axiom,(
% 1.32/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.32/0.56  fof(f43,plain,(
% 1.32/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f4])).
% 1.32/0.56  fof(f4,axiom,(
% 1.32/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.32/0.56  fof(f527,plain,(
% 1.32/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k1_xboole_0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f526,f131])).
% 1.32/0.56  fof(f131,plain,(
% 1.32/0.56    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f130,f44])).
% 1.32/0.56  fof(f44,plain,(
% 1.32/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f6])).
% 1.32/0.56  fof(f6,axiom,(
% 1.32/0.56    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.32/0.56  fof(f130,plain,(
% 1.32/0.56    ( ! [X2,X3] : (k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(X2,X2),X3)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f125,f44])).
% 1.32/0.56  fof(f125,plain,(
% 1.32/0.56    ( ! [X2,X3] : (k2_zfmisc_1(k5_xboole_0(X2,X2),X3) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X2,X3))) )),
% 1.32/0.56    inference(superposition,[],[f80,f71])).
% 1.32/0.56  fof(f71,plain,(
% 1.32/0.56    ( ! [X0] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 1.32/0.56    inference(definition_unfolding,[],[f45,f69])).
% 1.32/0.56  fof(f69,plain,(
% 1.32/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f46,f66])).
% 1.32/0.56  fof(f46,plain,(
% 1.32/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f7])).
% 1.32/0.56  fof(f7,axiom,(
% 1.32/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.56  fof(f45,plain,(
% 1.32/0.56    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.32/0.56    inference(cnf_transformation,[],[f13])).
% 1.32/0.56  % (4969)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.56  fof(f13,axiom,(
% 1.32/0.56    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.32/0.56  fof(f80,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X2))) )),
% 1.32/0.56    inference(backward_demodulation,[],[f74,f76])).
% 1.32/0.56  fof(f76,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_setfam_1(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) = k2_zfmisc_1(k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)),X2)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f62,f67,f67])).
% 1.32/0.56  fof(f62,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f11,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 1.32/0.56  fof(f74,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))),X2) = k5_xboole_0(k2_zfmisc_1(X0,X2),k1_setfam_1(k3_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f60,f68,f68])).
% 1.32/0.56  fof(f68,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f54,f67])).
% 1.32/0.56  fof(f54,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f3])).
% 1.32/0.56  fof(f3,axiom,(
% 1.32/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.56  fof(f60,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f12])).
% 1.32/0.56  fof(f12,axiom,(
% 1.32/0.56    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 1.32/0.56  fof(f526,plain,(
% 1.32/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f525,f40])).
% 1.32/0.56  fof(f40,plain,(
% 1.32/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.32/0.56    inference(cnf_transformation,[],[f21])).
% 1.32/0.56  fof(f21,axiom,(
% 1.32/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.32/0.56  fof(f525,plain,(
% 1.32/0.56    ( ! [X0] : (k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f521,f42])).
% 1.32/0.56  % (4978)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.56  fof(f42,plain,(
% 1.32/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f5])).
% 1.32/0.56  fof(f5,axiom,(
% 1.32/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.56  fof(f521,plain,(
% 1.32/0.56    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k5_relat_1(k1_xboole_0,X0) = k1_setfam_1(k3_enumset1(k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k5_relat_1(k1_xboole_0,X0),k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k5_relat_1(k1_xboole_0,X0))))) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.56    inference(superposition,[],[f96,f41])).
% 1.32/0.56  fof(f41,plain,(
% 1.32/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.32/0.56    inference(cnf_transformation,[],[f21])).
% 1.32/0.56  fof(f96,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k5_relat_1(X0,X1) = k1_setfam_1(k3_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(subsumption_resolution,[],[f95,f55])).
% 1.32/0.56  fof(f55,plain,(
% 1.32/0.56    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f32])).
% 1.32/0.56  fof(f32,plain,(
% 1.32/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.32/0.56    inference(flattening,[],[f31])).
% 1.32/0.56  fof(f31,plain,(
% 1.32/0.56    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.32/0.56    inference(ennf_transformation,[],[f16])).
% 1.32/0.56  fof(f16,axiom,(
% 1.32/0.56    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.32/0.56  fof(f95,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k5_relat_1(X0,X1) = k1_setfam_1(k3_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(k5_relat_1(X0,X1))))) | ~v1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(superposition,[],[f72,f50])).
% 1.32/0.56  fof(f50,plain,(
% 1.32/0.56    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f29])).
% 1.32/0.56  fof(f29,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.56    inference(flattening,[],[f28])).
% 1.32/0.56  fof(f28,plain,(
% 1.32/0.56    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f19])).
% 1.32/0.56  fof(f19,axiom,(
% 1.32/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.32/0.56  fof(f72,plain,(
% 1.32/0.56    ( ! [X0] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(definition_unfolding,[],[f48,f67])).
% 1.32/0.56  fof(f48,plain,(
% 1.32/0.56    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f26])).
% 1.32/0.56  fof(f26,plain,(
% 1.32/0.56    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 1.32/0.56    inference(ennf_transformation,[],[f17])).
% 1.32/0.56  fof(f17,axiom,(
% 1.32/0.56    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 1.32/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 1.32/0.56  fof(f157,plain,(
% 1.32/0.56    k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.32/0.56    inference(trivial_inequality_removal,[],[f152])).
% 1.32/0.56  fof(f152,plain,(
% 1.32/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.32/0.56    inference(superposition,[],[f38,f138])).
% 1.32/0.56  fof(f138,plain,(
% 1.32/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f137,f39])).
% 1.32/0.56  fof(f137,plain,(
% 1.32/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)),
% 1.32/0.56    inference(resolution,[],[f122,f47])).
% 1.32/0.56  fof(f122,plain,(
% 1.32/0.56    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.32/0.56    inference(subsumption_resolution,[],[f120,f37])).
% 1.32/0.56  fof(f120,plain,(
% 1.32/0.56    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 1.32/0.56    inference(resolution,[],[f116,f55])).
% 1.32/0.56  fof(f116,plain,(
% 1.32/0.56    ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 1.32/0.56    inference(forward_demodulation,[],[f115,f70])).
% 1.32/0.56  fof(f115,plain,(
% 1.32/0.56    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k3_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.32/0.56    inference(backward_demodulation,[],[f102,f112])).
% 1.32/0.56  fof(f112,plain,(
% 1.32/0.56    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k1_xboole_0)) )),
% 1.32/0.56    inference(forward_demodulation,[],[f111,f44])).
% 1.32/0.56  fof(f111,plain,(
% 1.32/0.56    ( ! [X2,X3] : (k1_xboole_0 = k2_zfmisc_1(X3,k5_xboole_0(X2,X2))) )),
% 1.32/0.56    inference(forward_demodulation,[],[f109,f44])).
% 1.32/0.56  fof(f109,plain,(
% 1.32/0.56    ( ! [X2,X3] : (k2_zfmisc_1(X3,k5_xboole_0(X2,X2)) = k5_xboole_0(k2_zfmisc_1(X3,X2),k2_zfmisc_1(X3,X2))) )),
% 1.32/0.56    inference(superposition,[],[f79,f71])).
% 1.32/0.56  fof(f79,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))))) )),
% 1.32/0.56    inference(backward_demodulation,[],[f73,f75])).
% 1.32/0.56  fof(f75,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k1_setfam_1(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) = k2_zfmisc_1(X2,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f63,f67,f67])).
% 1.32/0.56  fof(f63,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f11])).
% 1.32/0.56  fof(f73,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) = k5_xboole_0(k2_zfmisc_1(X2,X0),k1_setfam_1(k3_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))))) )),
% 1.32/0.56    inference(definition_unfolding,[],[f61,f68,f68])).
% 1.32/0.56  fof(f61,plain,(
% 1.32/0.56    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.32/0.56    inference(cnf_transformation,[],[f12])).
% 1.32/0.56  fof(f102,plain,(
% 1.32/0.56    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k3_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) | ~v1_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.32/0.56    inference(superposition,[],[f72,f97])).
% 1.32/0.56  fof(f97,plain,(
% 1.32/0.56    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 1.32/0.56    inference(resolution,[],[f93,f37])).
% 1.32/0.56  fof(f93,plain,(
% 1.32/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 1.32/0.56    inference(resolution,[],[f88,f81])).
% 1.32/0.56  fof(f81,plain,(
% 1.32/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.32/0.56    inference(resolution,[],[f58,f42])).
% 1.32/0.56  fof(f58,plain,(
% 1.32/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.32/0.56    inference(cnf_transformation,[],[f36])).
% 1.32/0.56  fof(f36,plain,(
% 1.32/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.56    inference(flattening,[],[f35])).
% 1.32/0.56  fof(f35,plain,(
% 1.32/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.56    inference(nnf_transformation,[],[f2])).
% 1.32/0.57  % (4967)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.57  fof(f2,axiom,(
% 1.32/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.57  fof(f88,plain,(
% 1.32/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(subsumption_resolution,[],[f87,f39])).
% 1.32/0.57  fof(f87,plain,(
% 1.32/0.57    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0) | ~v1_xboole_0(k1_xboole_0)) )),
% 1.32/0.57    inference(resolution,[],[f86,f47])).
% 1.32/0.57  fof(f86,plain,(
% 1.32/0.57    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(superposition,[],[f49,f41])).
% 1.32/0.57  fof(f49,plain,(
% 1.32/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f27])).
% 1.32/0.57  fof(f27,plain,(
% 1.32/0.57    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.57    inference(ennf_transformation,[],[f18])).
% 1.32/0.57  fof(f18,axiom,(
% 1.32/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 1.32/0.57  fof(f38,plain,(
% 1.32/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 1.32/0.57    inference(cnf_transformation,[],[f34])).
% 1.32/0.57  fof(f34,plain,(
% 1.32/0.57    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 1.32/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f33])).
% 1.32/0.57  fof(f33,plain,(
% 1.32/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 1.32/0.57    introduced(choice_axiom,[])).
% 1.32/0.57  fof(f24,plain,(
% 1.32/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 1.32/0.57    inference(ennf_transformation,[],[f23])).
% 1.32/0.57  fof(f23,negated_conjecture,(
% 1.32/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.32/0.57    inference(negated_conjecture,[],[f22])).
% 1.32/0.57  % (4974)Refutation not found, incomplete strategy% (4974)------------------------------
% 1.32/0.57  % (4974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (4974)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (4974)Memory used [KB]: 10618
% 1.32/0.57  % (4974)Time elapsed: 0.148 s
% 1.32/0.57  % (4974)------------------------------
% 1.32/0.57  % (4974)------------------------------
% 1.32/0.57  fof(f22,conjecture,(
% 1.32/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.32/0.57  fof(f37,plain,(
% 1.32/0.57    v1_relat_1(sK0)),
% 1.32/0.57    inference(cnf_transformation,[],[f34])).
% 1.32/0.57  % SZS output end Proof for theBenchmark
% 1.32/0.57  % (4980)------------------------------
% 1.32/0.57  % (4980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (4980)Termination reason: Refutation
% 1.32/0.57  
% 1.32/0.57  % (4980)Memory used [KB]: 6780
% 1.32/0.57  % (4980)Time elapsed: 0.135 s
% 1.32/0.57  % (4980)------------------------------
% 1.32/0.57  % (4980)------------------------------
% 1.32/0.57  % (4957)Success in time 0.203 s
%------------------------------------------------------------------------------
