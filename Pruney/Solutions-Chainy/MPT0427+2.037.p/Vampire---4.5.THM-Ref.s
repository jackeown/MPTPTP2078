%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:38 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 399 expanded)
%              Number of leaves         :   15 (  89 expanded)
%              Depth                    :   24
%              Number of atoms          :  193 (1039 expanded)
%              Number of equality atoms :   71 ( 277 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f648,plain,(
    $false ),
    inference(subsumption_resolution,[],[f647,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f647,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f639,f60])).

fof(f60,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f59,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f639,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) ),
    inference(backward_demodulation,[],[f589,f601])).

fof(f601,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f600,f282])).

fof(f282,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f280,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f280,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f279,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f279,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f46,f275])).

fof(f275,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f265,f184])).

fof(f184,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f45,f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f265,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f48,f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f600,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f569,f60])).

fof(f569,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | k1_xboole_0 = sK2 ),
    inference(backward_demodulation,[],[f278,f494])).

fof(f494,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f490,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f490,plain,(
    ! [X0] : ~ r2_hidden(X0,sK1) ),
    inference(subsumption_resolution,[],[f489,f467])).

fof(f467,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != X2
      | ~ r2_hidden(X3,X2) ) ),
    inference(forward_demodulation,[],[f465,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = X0 ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f465,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != X2
      | ~ r2_hidden(X3,k3_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X4,X2)))) ) ),
    inference(resolution,[],[f76,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f49,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f489,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK1 ) ),
    inference(forward_demodulation,[],[f486,f67])).

fof(f67,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f486,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | ~ r2_hidden(X0,k3_xboole_0(sK1,sK2)) ) ),
    inference(resolution,[],[f472,f41])).

fof(f472,plain,
    ( r1_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f469,f351])).

fof(f351,plain,
    ( r2_hidden(sK4(sK1,sK2),k1_xboole_0)
    | k1_xboole_0 = sK1
    | r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f306,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r2_hidden(sK4(sK1,sK2),X0)
      | r1_xboole_0(sK1,sK2) ) ),
    inference(resolution,[],[f83,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,
    ( r2_hidden(sK4(sK1,sK2),sK1)
    | r1_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f42,f67])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f306,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f33,f304])).

fof(f304,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f303,f33])).

fof(f303,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f290,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f290,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f278,f276])).

fof(f276,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f266,f185])).

fof(f185,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f45,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f266,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f48,f35])).

fof(f469,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f467])).

fof(f278,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f34,f275])).

fof(f34,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f589,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f502,f60])).

fof(f502,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f34,f494])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (798261248)
% 0.13/0.38  ipcrm: permission denied for id (798425100)
% 0.21/0.39  ipcrm: permission denied for id (798490641)
% 0.21/0.39  ipcrm: permission denied for id (798588949)
% 0.21/0.40  ipcrm: permission denied for id (798654490)
% 0.21/0.40  ipcrm: permission denied for id (798752799)
% 0.21/0.40  ipcrm: permission denied for id (798818336)
% 0.21/0.41  ipcrm: permission denied for id (798883875)
% 0.21/0.41  ipcrm: permission denied for id (798916645)
% 0.21/0.41  ipcrm: permission denied for id (798949414)
% 0.21/0.42  ipcrm: permission denied for id (799080493)
% 0.21/0.42  ipcrm: permission denied for id (799113262)
% 0.21/0.42  ipcrm: permission denied for id (799146031)
% 0.21/0.43  ipcrm: permission denied for id (799309877)
% 0.21/0.43  ipcrm: permission denied for id (799408184)
% 0.21/0.44  ipcrm: permission denied for id (799473721)
% 0.21/0.44  ipcrm: permission denied for id (799604799)
% 0.21/0.45  ipcrm: permission denied for id (799637568)
% 0.21/0.45  ipcrm: permission denied for id (799703108)
% 0.21/0.45  ipcrm: permission denied for id (799735877)
% 0.21/0.46  ipcrm: permission denied for id (799768646)
% 0.21/0.46  ipcrm: permission denied for id (799801415)
% 0.21/0.46  ipcrm: permission denied for id (799834184)
% 0.21/0.46  ipcrm: permission denied for id (799899723)
% 0.21/0.46  ipcrm: permission denied for id (799932492)
% 0.21/0.47  ipcrm: permission denied for id (799965261)
% 0.21/0.47  ipcrm: permission denied for id (800030800)
% 0.21/0.47  ipcrm: permission denied for id (800063569)
% 0.21/0.47  ipcrm: permission denied for id (800096338)
% 0.21/0.48  ipcrm: permission denied for id (800129107)
% 0.21/0.48  ipcrm: permission denied for id (800194646)
% 0.21/0.49  ipcrm: permission denied for id (800227418)
% 0.21/0.49  ipcrm: permission denied for id (800260188)
% 0.21/0.49  ipcrm: permission denied for id (800358495)
% 0.21/0.50  ipcrm: permission denied for id (800391266)
% 0.21/0.50  ipcrm: permission denied for id (800424036)
% 0.21/0.51  ipcrm: permission denied for id (800587880)
% 0.21/0.51  ipcrm: permission denied for id (800620649)
% 0.21/0.52  ipcrm: permission denied for id (800850032)
% 0.21/0.52  ipcrm: permission denied for id (800882802)
% 0.21/0.52  ipcrm: permission denied for id (800915572)
% 0.21/0.53  ipcrm: permission denied for id (800981112)
% 0.37/0.53  ipcrm: permission denied for id (801046651)
% 0.37/0.54  ipcrm: permission denied for id (801112189)
% 0.39/0.67  % (21922)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.39/0.67  % (21911)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.39/0.67  % (21898)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.39/0.68  % (21924)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.39/0.68  % (21900)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.39/0.68  % (21899)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.39/0.69  % (21907)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.39/0.69  % (21903)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.39/0.69  % (21901)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.39/0.69  % (21907)Refutation not found, incomplete strategy% (21907)------------------------------
% 0.39/0.69  % (21907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.69  % (21921)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.39/0.69  % (21915)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.39/0.69  % (21920)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.39/0.69  % (21907)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.69  
% 0.39/0.69  % (21907)Memory used [KB]: 10618
% 0.39/0.69  % (21907)Time elapsed: 0.096 s
% 0.39/0.69  % (21907)------------------------------
% 0.39/0.69  % (21907)------------------------------
% 0.39/0.69  % (21912)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.39/0.69  % (21905)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.39/0.69  % (21925)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.39/0.69  % (21897)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.39/0.69  % (21897)Refutation not found, incomplete strategy% (21897)------------------------------
% 0.39/0.69  % (21897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.69  % (21897)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.69  
% 0.39/0.69  % (21897)Memory used [KB]: 1663
% 0.39/0.69  % (21897)Time elapsed: 0.092 s
% 0.39/0.69  % (21897)------------------------------
% 0.39/0.69  % (21897)------------------------------
% 0.39/0.69  % (21923)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.39/0.69  % (21913)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.39/0.70  % (21918)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.39/0.70  % (21914)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.39/0.70  % (21904)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.39/0.70  % (21917)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.39/0.70  % (21914)Refutation not found, incomplete strategy% (21914)------------------------------
% 0.39/0.70  % (21914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (21914)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.70  
% 0.39/0.70  % (21914)Memory used [KB]: 10618
% 0.39/0.70  % (21914)Time elapsed: 0.113 s
% 0.39/0.70  % (21914)------------------------------
% 0.39/0.70  % (21914)------------------------------
% 0.39/0.70  % (21910)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.39/0.70  % (21926)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.39/0.71  % (21909)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.71  % (21916)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.39/0.71  % (21908)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.39/0.71  % (21902)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.39/0.71  % (21919)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.39/0.72  % (21906)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.39/0.72  % (21906)Refutation not found, incomplete strategy% (21906)------------------------------
% 0.39/0.72  % (21906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.72  % (21906)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.72  
% 0.39/0.72  % (21906)Memory used [KB]: 10618
% 0.39/0.72  % (21906)Time elapsed: 0.134 s
% 0.39/0.72  % (21906)------------------------------
% 0.39/0.72  % (21906)------------------------------
% 0.39/0.72  % (21903)Refutation found. Thanks to Tanya!
% 0.39/0.72  % SZS status Theorem for theBenchmark
% 0.39/0.73  % SZS output start Proof for theBenchmark
% 0.39/0.73  fof(f648,plain,(
% 0.39/0.73    $false),
% 0.39/0.73    inference(subsumption_resolution,[],[f647,f71])).
% 0.39/0.73  fof(f71,plain,(
% 0.39/0.73    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.39/0.73    inference(duplicate_literal_removal,[],[f70])).
% 0.39/0.73  fof(f70,plain,(
% 0.39/0.73    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.39/0.73    inference(resolution,[],[f53,f52])).
% 0.39/0.73  fof(f52,plain,(
% 0.39/0.73    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f29])).
% 0.39/0.73  fof(f29,plain,(
% 0.39/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.39/0.73    inference(ennf_transformation,[],[f1])).
% 0.39/0.73  fof(f1,axiom,(
% 0.39/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.39/0.73  fof(f53,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f29])).
% 0.39/0.73  fof(f647,plain,(
% 0.39/0.73    ~r1_tarski(sK0,sK0)),
% 0.39/0.73    inference(forward_demodulation,[],[f639,f60])).
% 0.39/0.73  fof(f60,plain,(
% 0.39/0.73    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.39/0.73    inference(subsumption_resolution,[],[f59,f36])).
% 0.39/0.73  fof(f36,plain,(
% 0.39/0.73    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f9])).
% 0.39/0.73  fof(f9,axiom,(
% 0.39/0.73    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.39/0.73  fof(f59,plain,(
% 0.39/0.73    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.39/0.73    inference(equality_resolution,[],[f47])).
% 0.39/0.73  fof(f47,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.39/0.73    inference(cnf_transformation,[],[f28])).
% 0.39/0.73  fof(f28,plain,(
% 0.39/0.73    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.39/0.73    inference(ennf_transformation,[],[f10])).
% 0.39/0.73  fof(f10,axiom,(
% 0.39/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.39/0.73  fof(f639,plain,(
% 0.39/0.73    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)),
% 0.39/0.73    inference(backward_demodulation,[],[f589,f601])).
% 0.39/0.73  fof(f601,plain,(
% 0.39/0.73    k1_xboole_0 = sK2),
% 0.39/0.73    inference(subsumption_resolution,[],[f600,f282])).
% 0.39/0.73  fof(f282,plain,(
% 0.39/0.73    r1_tarski(k1_setfam_1(sK2),sK0) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(resolution,[],[f280,f55])).
% 0.39/0.73  fof(f55,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f13])).
% 0.39/0.73  fof(f13,axiom,(
% 0.39/0.73    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.39/0.73  fof(f280,plain,(
% 0.39/0.73    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(subsumption_resolution,[],[f279,f32])).
% 0.39/0.73  fof(f32,plain,(
% 0.39/0.73    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.39/0.73    inference(cnf_transformation,[],[f20])).
% 0.39/0.73  fof(f20,plain,(
% 0.39/0.73    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.39/0.73    inference(flattening,[],[f19])).
% 0.39/0.73  fof(f19,plain,(
% 0.39/0.73    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.39/0.73    inference(ennf_transformation,[],[f17])).
% 0.39/0.73  fof(f17,negated_conjecture,(
% 0.39/0.73    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.39/0.73    inference(negated_conjecture,[],[f16])).
% 0.39/0.73  fof(f16,conjecture,(
% 0.39/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.39/0.73  fof(f279,plain,(
% 0.39/0.73    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(superposition,[],[f46,f275])).
% 0.39/0.73  fof(f275,plain,(
% 0.39/0.73    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(forward_demodulation,[],[f265,f184])).
% 0.39/0.73  fof(f184,plain,(
% 0.39/0.73    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.39/0.73    inference(resolution,[],[f45,f32])).
% 0.39/0.73  fof(f45,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f26])).
% 0.39/0.73  fof(f26,plain,(
% 0.39/0.73    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.39/0.73    inference(ennf_transformation,[],[f12])).
% 0.39/0.73  fof(f12,axiom,(
% 0.39/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.39/0.73  fof(f265,plain,(
% 0.39/0.73    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.39/0.73    inference(resolution,[],[f48,f32])).
% 0.39/0.73  fof(f48,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f28])).
% 0.39/0.73  fof(f46,plain,(
% 0.39/0.73    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f27])).
% 0.39/0.73  fof(f27,plain,(
% 0.39/0.73    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.39/0.73    inference(ennf_transformation,[],[f11])).
% 0.39/0.73  fof(f11,axiom,(
% 0.39/0.73    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.39/0.73  fof(f600,plain,(
% 0.39/0.73    ~r1_tarski(k1_setfam_1(sK2),sK0) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(forward_demodulation,[],[f569,f60])).
% 0.39/0.73  fof(f569,plain,(
% 0.39/0.73    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(backward_demodulation,[],[f278,f494])).
% 0.39/0.73  fof(f494,plain,(
% 0.39/0.73    k1_xboole_0 = sK1),
% 0.39/0.73    inference(resolution,[],[f490,f37])).
% 0.39/0.73  fof(f37,plain,(
% 0.39/0.73    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.39/0.73    inference(cnf_transformation,[],[f21])).
% 0.39/0.73  fof(f21,plain,(
% 0.39/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.39/0.73    inference(ennf_transformation,[],[f3])).
% 0.39/0.73  fof(f3,axiom,(
% 0.39/0.73    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.39/0.73  fof(f490,plain,(
% 0.39/0.73    ( ! [X0] : (~r2_hidden(X0,sK1)) )),
% 0.39/0.73    inference(subsumption_resolution,[],[f489,f467])).
% 0.39/0.73  fof(f467,plain,(
% 0.39/0.73    ( ! [X2,X3] : (k1_xboole_0 != X2 | ~r2_hidden(X3,X2)) )),
% 0.39/0.73    inference(forward_demodulation,[],[f465,f65])).
% 0.39/0.73  fof(f65,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) = X0) )),
% 0.39/0.73    inference(resolution,[],[f43,f57])).
% 0.39/0.73  fof(f57,plain,(
% 0.39/0.73    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.39/0.73    inference(definition_unfolding,[],[f38,f40])).
% 0.39/0.73  fof(f40,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f8])).
% 0.39/0.73  fof(f8,axiom,(
% 0.39/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.39/0.73  fof(f38,plain,(
% 0.39/0.73    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f6])).
% 0.39/0.73  fof(f6,axiom,(
% 0.39/0.73    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.39/0.73  fof(f43,plain,(
% 0.39/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.39/0.73    inference(cnf_transformation,[],[f23])).
% 0.39/0.73  fof(f23,plain,(
% 0.39/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.39/0.73    inference(ennf_transformation,[],[f4])).
% 0.39/0.73  fof(f4,axiom,(
% 0.39/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.39/0.73  fof(f465,plain,(
% 0.39/0.73    ( ! [X4,X2,X3] : (k1_xboole_0 != X2 | ~r2_hidden(X3,k3_xboole_0(X2,k5_xboole_0(X2,k4_xboole_0(X4,X2))))) )),
% 0.39/0.73    inference(resolution,[],[f76,f41])).
% 0.39/0.73  fof(f41,plain,(
% 0.39/0.73    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f22])).
% 0.39/0.73  fof(f22,plain,(
% 0.39/0.73    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.39/0.73    inference(ennf_transformation,[],[f18])).
% 0.39/0.73  fof(f18,plain,(
% 0.39/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.73    inference(rectify,[],[f2])).
% 0.39/0.73  fof(f2,axiom,(
% 0.39/0.73    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.39/0.73  fof(f76,plain,(
% 0.39/0.73    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | k1_xboole_0 != X0) )),
% 0.39/0.73    inference(superposition,[],[f49,f58])).
% 0.39/0.73  fof(f58,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.39/0.73    inference(definition_unfolding,[],[f39,f40])).
% 0.39/0.73  fof(f39,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.39/0.73    inference(cnf_transformation,[],[f5])).
% 0.39/0.73  fof(f5,axiom,(
% 0.39/0.73    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.39/0.73  fof(f49,plain,(
% 0.39/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f7])).
% 0.39/0.73  fof(f7,axiom,(
% 0.39/0.73    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.39/0.73  fof(f489,plain,(
% 0.39/0.73    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_xboole_0 = sK1) )),
% 0.39/0.73    inference(forward_demodulation,[],[f486,f67])).
% 0.39/0.73  fof(f67,plain,(
% 0.39/0.73    sK1 = k3_xboole_0(sK1,sK2)),
% 0.39/0.73    inference(resolution,[],[f43,f33])).
% 0.39/0.73  fof(f33,plain,(
% 0.39/0.73    r1_tarski(sK1,sK2)),
% 0.39/0.73    inference(cnf_transformation,[],[f20])).
% 0.39/0.73  fof(f486,plain,(
% 0.39/0.73    ( ! [X0] : (k1_xboole_0 = sK1 | ~r2_hidden(X0,k3_xboole_0(sK1,sK2))) )),
% 0.39/0.73    inference(resolution,[],[f472,f41])).
% 0.39/0.73  fof(f472,plain,(
% 0.39/0.73    r1_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 0.39/0.73    inference(resolution,[],[f469,f351])).
% 0.39/0.73  fof(f351,plain,(
% 0.39/0.73    r2_hidden(sK4(sK1,sK2),k1_xboole_0) | k1_xboole_0 = sK1 | r1_xboole_0(sK1,sK2)),
% 0.39/0.73    inference(resolution,[],[f306,f86])).
% 0.39/0.73  fof(f86,plain,(
% 0.39/0.73    ( ! [X0] : (~r1_tarski(sK1,X0) | r2_hidden(sK4(sK1,sK2),X0) | r1_xboole_0(sK1,sK2)) )),
% 0.39/0.73    inference(resolution,[],[f83,f51])).
% 0.39/0.73  fof(f51,plain,(
% 0.39/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f29])).
% 0.39/0.73  fof(f83,plain,(
% 0.39/0.73    r2_hidden(sK4(sK1,sK2),sK1) | r1_xboole_0(sK1,sK2)),
% 0.39/0.73    inference(superposition,[],[f42,f67])).
% 0.39/0.73  fof(f42,plain,(
% 0.39/0.73    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f22])).
% 0.39/0.73  fof(f306,plain,(
% 0.39/0.73    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.39/0.73    inference(superposition,[],[f33,f304])).
% 0.39/0.73  fof(f304,plain,(
% 0.39/0.73    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.39/0.73    inference(subsumption_resolution,[],[f303,f33])).
% 0.39/0.73  fof(f303,plain,(
% 0.39/0.73    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 0.39/0.73    inference(duplicate_literal_removal,[],[f302])).
% 0.39/0.73  fof(f302,plain,(
% 0.39/0.73    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 0.39/0.73    inference(resolution,[],[f290,f44])).
% 0.39/0.73  fof(f44,plain,(
% 0.39/0.73    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.39/0.73    inference(cnf_transformation,[],[f25])).
% 0.39/0.73  fof(f25,plain,(
% 0.39/0.73    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.39/0.73    inference(flattening,[],[f24])).
% 0.39/0.73  fof(f24,plain,(
% 0.39/0.73    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.39/0.73    inference(ennf_transformation,[],[f15])).
% 0.39/0.73  fof(f15,axiom,(
% 0.39/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.39/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.39/0.73  fof(f290,plain,(
% 0.39/0.73    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.39/0.73    inference(superposition,[],[f278,f276])).
% 0.39/0.73  fof(f276,plain,(
% 0.39/0.73    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 0.39/0.73    inference(forward_demodulation,[],[f266,f185])).
% 0.39/0.73  fof(f185,plain,(
% 0.39/0.73    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.39/0.73    inference(resolution,[],[f45,f35])).
% 0.39/0.73  fof(f35,plain,(
% 0.39/0.73    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.39/0.73    inference(cnf_transformation,[],[f20])).
% 0.39/0.73  fof(f266,plain,(
% 0.39/0.73    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 0.39/0.73    inference(resolution,[],[f48,f35])).
% 0.39/0.73  fof(f469,plain,(
% 0.39/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.39/0.73    inference(equality_resolution,[],[f467])).
% 0.39/0.73  fof(f278,plain,(
% 0.39/0.73    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.39/0.73    inference(superposition,[],[f34,f275])).
% 0.39/0.73  fof(f34,plain,(
% 0.39/0.73    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.39/0.73    inference(cnf_transformation,[],[f20])).
% 0.39/0.73  fof(f589,plain,(
% 0.39/0.73    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.39/0.73    inference(forward_demodulation,[],[f502,f60])).
% 0.39/0.73  fof(f502,plain,(
% 0.39/0.73    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.39/0.73    inference(backward_demodulation,[],[f34,f494])).
% 0.39/0.73  % SZS output end Proof for theBenchmark
% 0.39/0.73  % (21903)------------------------------
% 0.39/0.73  % (21903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.73  % (21903)Termination reason: Refutation
% 0.39/0.73  
% 0.39/0.73  % (21903)Memory used [KB]: 6652
% 0.39/0.73  % (21903)Time elapsed: 0.120 s
% 0.39/0.73  % (21903)------------------------------
% 0.39/0.73  % (21903)------------------------------
% 0.39/0.73  % (21733)Success in time 0.371 s
%------------------------------------------------------------------------------
