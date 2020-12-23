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
% DateTime   : Thu Dec  3 12:46:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  100 (1080 expanded)
%              Number of leaves         :   18 ( 315 expanded)
%              Depth                    :   23
%              Number of atoms          :  222 (3514 expanded)
%              Number of equality atoms :   88 ( 724 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f174,f139])).

fof(f139,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(backward_demodulation,[],[f41,f138])).

fof(f138,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f43,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f137,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f135,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f135,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f134,f111])).

fof(f111,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f67,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f71,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f71,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f53,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f67,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f110,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = k1_tarski(sK3(sK2))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f57,f109])).

fof(f109,plain,
    ( sK2 = k2_xboole_0(k1_tarski(sK3(sK2)),sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f105,plain,
    ( v1_xboole_0(sK1)
    | sK2 = k2_xboole_0(k1_tarski(sK3(sK2)),sK2) ),
    inference(resolution,[],[f97,f43])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0 ) ),
    inference(resolution,[],[f78,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f76,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f76,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0 ) ),
    inference(resolution,[],[f55,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_xboole_0(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_xboole_0(X0,X1)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

fof(f134,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f118,f117])).

fof(f117,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f113,f85])).

fof(f85,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f58,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f113,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f60,f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f118,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f44,f116])).

fof(f116,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f112,f84])).

fof(f84,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f58,f41])).

fof(f112,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f60,f41])).

fof(f44,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f174,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(subsumption_resolution,[],[f172,f165])).

fof(f165,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f164,f150])).

fof(f150,plain,(
    sK0 = k8_setfam_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f142,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f66,f63])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f142,plain,(
    r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f68,f138])).

fof(f68,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f62,f41])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f164,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) ),
    inference(forward_demodulation,[],[f154,f155])).

fof(f155,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f153,f129])).

fof(f129,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f127,f42])).

fof(f127,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f89,f117])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_setfam_1(X1,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f59,f62])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f153,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f148,f150])).

fof(f148,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f126,f138])).

fof(f126,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f44,f117])).

fof(f154,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(backward_demodulation,[],[f141,f150])).

fof(f141,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f44,f138])).

fof(f172,plain,
    ( r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f89,f150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:42:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (13734)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (13734)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (13750)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f174,f139])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(backward_demodulation,[],[f41,f138])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f137,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f33,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f18])).
% 0.22/0.52  fof(f18,conjecture,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f136])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(resolution,[],[f135,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f134,f111])).
% 0.22/0.52  fof(f111,plain,(
% 0.22/0.52    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 0.22/0.52    inference(subsumption_resolution,[],[f110,f73])).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.22/0.52    inference(backward_demodulation,[],[f67,f72])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f71,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.52    inference(superposition,[],[f53,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    inference(rectify,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.52    inference(equality_resolution,[],[f64])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.52  fof(f110,plain,(
% 0.22/0.52    k1_xboole_0 != sK2 | k1_xboole_0 = k1_tarski(sK3(sK2)) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f57,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    sK2 = k2_xboole_0(k1_tarski(sK3(sK2)),sK2) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(resolution,[],[f105,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    v1_xboole_0(sK1) | sK2 = k2_xboole_0(k1_tarski(sK3(sK2)),sK2)),
% 0.22/0.52    inference(resolution,[],[f97,f43])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0) )),
% 0.22/0.52    inference(resolution,[],[f78,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0 | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f76,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(X0) | k2_xboole_0(k1_tarski(sK3(X0)),X0) = X0) )),
% 0.22/0.52    inference(resolution,[],[f55,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f36,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.52    inference(rectify,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_zfmisc_1)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(X0,X1) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_xboole_0(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (k1_xboole_0 = k2_xboole_0(X0,X1) => k1_xboole_0 = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f118,f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(forward_demodulation,[],[f113,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.22/0.52    inference(resolution,[],[f58,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.52  fof(f113,plain,(
% 0.22/0.52    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.22/0.52    inference(resolution,[],[f60,f42])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(superposition,[],[f44,f116])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 0.22/0.52    inference(forward_demodulation,[],[f112,f84])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.22/0.52    inference(resolution,[],[f58,f41])).
% 0.22/0.52  fof(f112,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f60,f41])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f174,plain,(
% 0.22/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f172,f165])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ~r1_tarski(sK0,sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f164,f150])).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    sK0 = k8_setfam_1(sK0,k1_xboole_0)),
% 0.22/0.52    inference(resolution,[],[f142,f80])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(resolution,[],[f66,f63])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(equality_resolution,[],[f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    r1_tarski(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(backward_demodulation,[],[f68,f138])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(resolution,[],[f62,f41])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)),
% 0.22/0.52    inference(forward_demodulation,[],[f154,f155])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    k1_xboole_0 = sK2),
% 0.22/0.52    inference(subsumption_resolution,[],[f153,f129])).
% 0.22/0.52  fof(f129,plain,(
% 0.22/0.52    r1_tarski(k1_setfam_1(sK2),sK0) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(subsumption_resolution,[],[f127,f42])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f89,f117])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k8_setfam_1(X1,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 0.22/0.52    inference(resolution,[],[f59,f62])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(sK2),sK0) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(backward_demodulation,[],[f148,f150])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(backward_demodulation,[],[f126,f138])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.22/0.52    inference(superposition,[],[f44,f117])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.22/0.52    inference(backward_demodulation,[],[f141,f150])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.22/0.52    inference(backward_demodulation,[],[f44,f138])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.52    inference(superposition,[],[f89,f150])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (13734)------------------------------
% 0.22/0.52  % (13734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13734)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (13734)Memory used [KB]: 6268
% 0.22/0.52  % (13734)Time elapsed: 0.064 s
% 0.22/0.52  % (13734)------------------------------
% 0.22/0.52  % (13734)------------------------------
% 0.22/0.52  % (13726)Success in time 0.159 s
%------------------------------------------------------------------------------
