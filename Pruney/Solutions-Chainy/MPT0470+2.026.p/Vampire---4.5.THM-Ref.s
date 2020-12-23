%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 163 expanded)
%              Number of leaves         :   17 (  46 expanded)
%              Depth                    :   16
%              Number of atoms          :  183 ( 340 expanded)
%              Number of equality atoms :   75 ( 154 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f340,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f333])).

fof(f333,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f308,f317])).

% (15901)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f317,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f316,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f45,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f316,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f315,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).

fof(f315,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f312,f128])).

fof(f128,plain,(
    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f127,f49])).

fof(f127,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f118,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f94,f36])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f40,f46])).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f44,f48])).

fof(f48,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (15908)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f312,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) ),
    inference(resolution,[],[f171,f49])).

fof(f171,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k5_relat_1(sK0,X0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))) ) ),
    inference(resolution,[],[f150,f51])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(sK0,X0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))) ) ),
    inference(resolution,[],[f84,f36])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k5_relat_1(X1,X2) = k1_setfam_1(k1_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2))))) ) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ) ),
    inference(definition_unfolding,[],[f50,f56])).

fof(f50,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f308,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f304])).

fof(f304,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f37,f302])).

fof(f302,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f301,f57])).

fof(f301,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f300,f64])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f62,f49])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f300,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) ),
    inference(forward_demodulation,[],[f297,f180])).

fof(f180,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f179,f49])).

fof(f179,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f174,f51])).

fof(f174,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f114,f36])).

fof(f114,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) ) ),
    inference(resolution,[],[f87,f46])).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f85,f47])).

fof(f47,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
      | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f43,f48])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f297,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) ),
    inference(resolution,[],[f162,f49])).

fof(f162,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k5_relat_1(X0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) ) ),
    inference(resolution,[],[f147,f51])).

fof(f147,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0))))) ) ),
    inference(resolution,[],[f84,f36])).

fof(f37,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (15907)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (15909)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (15899)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (15898)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (15896)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (15895)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (15923)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (15915)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (15899)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f340,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f333])).
% 0.20/0.51  fof(f333,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0),
% 0.20/0.51    inference(superposition,[],[f308,f317])).
% 0.20/0.51  % (15901)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  fof(f317,plain,(
% 0.20/0.51    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.51    inference(forward_demodulation,[],[f316,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f45,f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f54,f55])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.51  fof(f316,plain,(
% 0.20/0.51    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f315,f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(resolution,[],[f63,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X1,X0)) )),
% 0.20/0.51    inference(resolution,[],[f53,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_zfmisc_1)).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)))),
% 0.20/0.51    inference(forward_demodulation,[],[f312,f128])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.51    inference(resolution,[],[f127,f49])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.51    inference(resolution,[],[f118,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k2_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.20/0.51    inference(resolution,[],[f94,f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    v1_relat_1(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.51    inference(negated_conjecture,[],[f19])).
% 0.20/0.51  fof(f19,conjecture,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(k5_relat_1(X0,k1_xboole_0))) )),
% 0.20/0.51    inference(resolution,[],[f78,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(resolution,[],[f40,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(flattening,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(superposition,[],[f44,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,axiom,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  % (15908)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 0.20/0.51  fof(f312,plain,(
% 0.20/0.51    k5_relat_1(sK0,k1_xboole_0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0)))))),
% 0.20/0.51    inference(resolution,[],[f171,f49])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k5_relat_1(sK0,X0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0)))))) )),
% 0.20/0.51    inference(resolution,[],[f150,f51])).
% 0.20/0.51  fof(f150,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(sK0,X0) = k1_setfam_1(k1_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0)))))) )),
% 0.20/0.51    inference(resolution,[],[f84,f36])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k5_relat_1(X1,X2) = k1_setfam_1(k1_enumset1(k5_relat_1(X1,X2),k5_relat_1(X1,X2),k2_zfmisc_1(k1_relat_1(k5_relat_1(X1,X2)),k2_relat_1(k5_relat_1(X1,X2)))))) )),
% 0.20/0.51    inference(resolution,[],[f58,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(flattening,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0) )),
% 0.20/0.51    inference(definition_unfolding,[],[f50,f56])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f304])).
% 0.20/0.51  fof(f304,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.20/0.51    inference(backward_demodulation,[],[f37,f302])).
% 0.20/0.51  fof(f302,plain,(
% 0.20/0.51    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.51    inference(forward_demodulation,[],[f301,f57])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k1_xboole_0))),
% 0.20/0.51    inference(forward_demodulation,[],[f300,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f62,f49])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f52,f41])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.20/0.51  fof(f300,plain,(
% 0.20/0.51    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))),
% 0.20/0.51    inference(forward_demodulation,[],[f297,f180])).
% 0.20/0.51  fof(f180,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    inference(resolution,[],[f179,f49])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    inference(resolution,[],[f174,f51])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.20/0.51    inference(resolution,[],[f114,f36])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0))) )),
% 0.20/0.51    inference(resolution,[],[f87,f46])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f85,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_relat_1(X0)) | k1_relat_1(k1_xboole_0) = k1_relat_1(k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.20/0.51    inference(superposition,[],[f43,f48])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    k5_relat_1(k1_xboole_0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))))),
% 0.20/0.52    inference(resolution,[],[f162,f49])).
% 0.20/0.52  fof(f162,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k5_relat_1(X0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0)))))) )),
% 0.20/0.52    inference(resolution,[],[f147,f51])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,sK0) = k1_setfam_1(k1_enumset1(k5_relat_1(X0,sK0),k5_relat_1(X0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,sK0)),k2_relat_1(k5_relat_1(X0,sK0)))))) )),
% 0.20/0.52    inference(resolution,[],[f84,f36])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f33])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (15899)------------------------------
% 0.20/0.52  % (15899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (15899)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (15899)Memory used [KB]: 1918
% 0.20/0.52  % (15899)Time elapsed: 0.095 s
% 0.20/0.52  % (15899)------------------------------
% 0.20/0.52  % (15899)------------------------------
% 0.20/0.52  % (15922)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (15904)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (15893)Success in time 0.162 s
%------------------------------------------------------------------------------
