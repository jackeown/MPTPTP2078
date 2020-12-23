%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 434 expanded)
%              Number of leaves         :   19 ( 125 expanded)
%              Depth                    :   18
%              Number of atoms          :  197 ( 915 expanded)
%              Number of equality atoms :   94 ( 498 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f516,plain,(
    $false ),
    inference(subsumption_resolution,[],[f515,f199])).

fof(f199,plain,(
    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f185])).

fof(f185,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f40,f184])).

fof(f184,plain,(
    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f183,f45])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f183,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f181,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f181,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(backward_demodulation,[],[f152,f178])).

fof(f178,plain,(
    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f113,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f61,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f61,plain,(
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

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f113,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f111,f42])).

fof(f42,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f111,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f93,f72])).

fof(f72,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f47,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f51,f39])).

fof(f39,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f152,plain,(
    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0)))) ),
    inference(resolution,[],[f108,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f108,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(resolution,[],[f77,f72])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,sK0)) ) ),
    inference(resolution,[],[f58,f39])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1))
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f40,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f515,plain,(
    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f492,f122])).

fof(f122,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f121,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f83,f45])).

fof(f83,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f57,f46])).

fof(f46,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f121,plain,(
    k4_relat_1(k1_xboole_0) = k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f118,f85])).

fof(f118,plain,(
    k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(sK0,sK0)) ),
    inference(resolution,[],[f102,f39])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_xboole_0(k4_relat_1(X0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(X0,sK0)) ) ),
    inference(resolution,[],[f71,f39])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f70,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f52,f54])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).

fof(f492,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f273,f489])).

fof(f489,plain,(
    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f488,f45])).

fof(f488,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f486,f69])).

fof(f486,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))) ),
    inference(backward_demodulation,[],[f375,f481])).

fof(f481,plain,(
    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(resolution,[],[f260,f86])).

fof(f260,plain,(
    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f246,f253])).

fof(f253,plain,(
    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f125,f39])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f99,f122])).

fof(f99,plain,(
    ! [X1] :
      ( k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f53,f72])).

% (5326)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f246,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f240,f42])).

fof(f240,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f95,f72])).

fof(f95,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f51,f73])).

fof(f73,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f375,plain,(
    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))))) ),
    inference(resolution,[],[f261,f50])).

fof(f261,plain,(
    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f215,f253])).

fof(f215,plain,(
    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f79,f72])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k5_relat_1(X0,k4_relat_1(sK0))) ) ),
    inference(resolution,[],[f73,f58])).

fof(f273,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f272,f253])).

fof(f272,plain,(
    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f266,f122])).

fof(f266,plain,(
    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f101,f72])).

fof(f101,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X2)) ) ),
    inference(forward_demodulation,[],[f100,f75])).

fof(f75,plain,(
    sK0 = k4_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f100,plain,(
    ! [X2] :
      ( k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f53,f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (5304)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (5319)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.52  % (5309)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (5313)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (5310)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (5329)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (5331)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (5305)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (5318)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (5330)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (5307)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (5306)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (5302)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (5303)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (5328)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (5320)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (5311)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (5321)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (5322)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (5327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (5314)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (5323)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (5317)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (5312)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (5315)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (5312)Refutation not found, incomplete strategy% (5312)------------------------------
% 0.21/0.55  % (5312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5312)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5312)Memory used [KB]: 10618
% 0.21/0.55  % (5312)Time elapsed: 0.148 s
% 0.21/0.55  % (5312)------------------------------
% 0.21/0.55  % (5312)------------------------------
% 0.21/0.55  % (5331)Refutation not found, incomplete strategy% (5331)------------------------------
% 0.21/0.55  % (5331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (5331)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (5331)Memory used [KB]: 1663
% 0.21/0.55  % (5331)Time elapsed: 0.129 s
% 0.21/0.55  % (5331)------------------------------
% 0.21/0.55  % (5331)------------------------------
% 0.21/0.56  % (5318)Refutation not found, incomplete strategy% (5318)------------------------------
% 0.21/0.56  % (5318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5318)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5318)Memory used [KB]: 10618
% 0.21/0.56  % (5318)Time elapsed: 0.158 s
% 0.21/0.56  % (5318)------------------------------
% 0.21/0.56  % (5318)------------------------------
% 0.21/0.56  % (5330)Refutation not found, incomplete strategy% (5330)------------------------------
% 0.21/0.56  % (5330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (5330)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (5330)Memory used [KB]: 10746
% 0.21/0.56  % (5330)Time elapsed: 0.157 s
% 0.21/0.56  % (5330)------------------------------
% 0.21/0.56  % (5330)------------------------------
% 0.21/0.56  % (5324)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.56  % (5325)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (5316)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (5308)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (5309)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f516,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f515,f199])).
% 0.21/0.57  fof(f199,plain,(
% 0.21/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f185])).
% 0.21/0.57  fof(f185,plain,(
% 0.21/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f40,f184])).
% 0.21/0.57  fof(f184,plain,(
% 0.21/0.57    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    inference(forward_demodulation,[],[f183,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f181,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(flattening,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 0.21/0.57    inference(backward_demodulation,[],[f152,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.57    inference(resolution,[],[f113,f86])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.57    inference(resolution,[],[f61,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f111,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,axiom,(
% 0.21/0.57    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k1_relat_1(k1_xboole_0))),
% 0.21/0.57    inference(resolution,[],[f93,f72])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    v1_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(resolution,[],[f47,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(k1_relat_1(k5_relat_1(X0,sK0)),k1_relat_1(X0))) )),
% 0.21/0.57    inference(resolution,[],[f51,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    v1_relat_1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.57    inference(negated_conjecture,[],[f21])).
% 0.21/0.57  fof(f21,conjecture,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    k5_relat_1(k1_xboole_0,sK0) = k3_xboole_0(k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))),
% 0.21/0.57    inference(resolution,[],[f108,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    v1_relat_1(k5_relat_1(k1_xboole_0,sK0))),
% 0.21/0.57    inference(resolution,[],[f77,f72])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,sK0))) )),
% 0.21/0.57    inference(resolution,[],[f58,f39])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f515,plain,(
% 0.21/0.57    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f492,f122])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    k1_xboole_0 = k4_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f121,f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f83,f45])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.21/0.57    inference(superposition,[],[f57,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    k4_relat_1(k1_xboole_0) = k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0))),
% 0.21/0.57    inference(forward_demodulation,[],[f118,f85])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    k4_xboole_0(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(sK0,sK0))),
% 0.21/0.57    inference(resolution,[],[f102,f39])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k4_xboole_0(k4_relat_1(X0),k4_relat_1(sK0)) = k4_relat_1(k4_xboole_0(X0,sK0))) )),
% 0.21/0.57    inference(resolution,[],[f71,f39])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f70,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(forward_demodulation,[],[f52,f54])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_relat_1)).
% 0.21/0.57  fof(f492,plain,(
% 0.21/0.57    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f273,f489])).
% 0.21/0.57  fof(f489,plain,(
% 0.21/0.57    k1_xboole_0 = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.57    inference(forward_demodulation,[],[f488,f45])).
% 0.21/0.57  fof(f488,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f486,f69])).
% 0.21/0.57  fof(f486,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))),
% 0.21/0.57    inference(backward_demodulation,[],[f375,f481])).
% 0.21/0.57  fof(f481,plain,(
% 0.21/0.57    k1_xboole_0 = k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    inference(resolution,[],[f260,f86])).
% 0.21/0.57  fof(f260,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k1_xboole_0)),
% 0.21/0.57    inference(backward_demodulation,[],[f246,f253])).
% 0.21/0.57  fof(f253,plain,(
% 0.21/0.57    k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),
% 0.21/0.57    inference(resolution,[],[f125,f39])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(X1))) )),
% 0.21/0.57    inference(backward_demodulation,[],[f99,f122])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X1] : (k4_relat_1(k5_relat_1(X1,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.57    inference(resolution,[],[f53,f72])).
% 0.21/0.57  % (5326)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_xboole_0)),
% 0.21/0.57    inference(forward_demodulation,[],[f240,f42])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))),k1_relat_1(k1_xboole_0))),
% 0.21/0.57    inference(resolution,[],[f95,f72])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    ( ! [X2] : (~v1_relat_1(X2) | r1_tarski(k1_relat_1(k5_relat_1(X2,k4_relat_1(sK0))),k1_relat_1(X2))) )),
% 0.21/0.57    inference(resolution,[],[f51,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f48,f39])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.57  fof(f375,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k3_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))),
% 0.21/0.57    inference(resolution,[],[f261,f50])).
% 0.21/0.57  fof(f261,plain,(
% 0.21/0.57    v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    inference(backward_demodulation,[],[f215,f253])).
% 0.21/0.57  fof(f215,plain,(
% 0.21/0.57    v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.21/0.57    inference(resolution,[],[f79,f72])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k5_relat_1(X0,k4_relat_1(sK0)))) )),
% 0.21/0.57    inference(resolution,[],[f73,f58])).
% 0.21/0.57  fof(f273,plain,(
% 0.21/0.57    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))),
% 0.21/0.57    inference(forward_demodulation,[],[f272,f253])).
% 0.21/0.57  fof(f272,plain,(
% 0.21/0.57    k5_relat_1(sK0,k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0)))),
% 0.21/0.57    inference(forward_demodulation,[],[f266,f122])).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    k4_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(k1_xboole_0))),
% 0.21/0.57    inference(resolution,[],[f101,f72])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ( ! [X2] : (~v1_relat_1(X2) | k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(sK0,k4_relat_1(X2))) )),
% 0.21/0.57    inference(forward_demodulation,[],[f100,f75])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    sK0 = k4_relat_1(k4_relat_1(sK0))),
% 0.21/0.57    inference(resolution,[],[f49,f39])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,axiom,(
% 0.21/0.57    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    ( ! [X2] : (k4_relat_1(k5_relat_1(X2,k4_relat_1(sK0))) = k5_relat_1(k4_relat_1(k4_relat_1(sK0)),k4_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.21/0.57    inference(resolution,[],[f53,f73])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (5309)------------------------------
% 0.21/0.57  % (5309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (5309)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (5309)Memory used [KB]: 2174
% 0.21/0.57  % (5309)Time elapsed: 0.168 s
% 0.21/0.57  % (5309)------------------------------
% 0.21/0.57  % (5309)------------------------------
% 0.21/0.58  % (5301)Success in time 0.217 s
%------------------------------------------------------------------------------
