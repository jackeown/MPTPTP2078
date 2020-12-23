%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:33 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 434 expanded)
%              Number of leaves         :   16 ( 113 expanded)
%              Depth                    :   17
%              Number of atoms          :  173 ( 958 expanded)
%              Number of equality atoms :   55 ( 283 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f673,plain,(
    $false ),
    inference(subsumption_resolution,[],[f657,f201])).

fof(f201,plain,(
    k1_xboole_0 != sK1 ),
    inference(resolution,[],[f192,f80])).

fof(f80,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f64])).

fof(f64,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f28,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

fof(f192,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f180,f177])).

fof(f177,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f174,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f174,plain,(
    ! [X0] : ~ r2_hidden(X0,k4_xboole_0(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f169,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k4_xboole_0(X1,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f144,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f144,plain,(
    ! [X6] : r1_xboole_0(X6,k4_xboole_0(X6,X6)) ),
    inference(trivial_inequality_removal,[],[f143])).

fof(f143,plain,(
    ! [X6] :
      ( X6 != X6
      | r1_xboole_0(X6,k4_xboole_0(X6,X6)) ) ),
    inference(superposition,[],[f50,f111])).

fof(f111,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f66,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f42,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f169,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK1,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(superposition,[],[f79,f113])).

fof(f113,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f66,f87])).

fof(f87,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f86,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f30,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f83,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f33])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f180,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK1,sK1),X2) ),
    inference(resolution,[],[f174,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f657,plain,(
    k1_xboole_0 = sK1 ),
    inference(superposition,[],[f512,f388])).

fof(f388,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f358,f360])).

fof(f360,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f350,f200])).

fof(f200,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(resolution,[],[f191,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f191,plain,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f179,f177])).

fof(f179,plain,(
    ! [X1] : r1_xboole_0(X1,k4_xboole_0(sK1,sK1)) ),
    inference(resolution,[],[f174,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f350,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f63,f250])).

fof(f250,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f176,f32])).

fof(f176,plain,(
    ! [X2,X3] : ~ r2_hidden(X3,k4_xboole_0(X2,X2)) ),
    inference(subsumption_resolution,[],[f171,f145])).

fof(f171,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(X2,X2))
      | r2_hidden(X3,X2) ) ),
    inference(superposition,[],[f79,f111])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f358,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f63,f301])).

fof(f301,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f294,f201])).

fof(f294,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f112,f288])).

fof(f288,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f43,f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f112,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f66,f65])).

fof(f65,plain,
    ( r1_tarski(sK1,k3_subset_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f27,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f512,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f94,f73])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0 ) ),
    inference(resolution,[],[f56,f51])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:37:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (10338)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (10348)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (10346)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (10362)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.17/0.51  % (10337)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.17/0.52  % (10340)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.17/0.52  % (10354)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.17/0.52  % (10349)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.17/0.53  % (10339)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.17/0.53  % (10357)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.54  % (10347)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (10341)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (10357)Refutation not found, incomplete strategy% (10357)------------------------------
% 1.31/0.54  % (10357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (10357)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (10357)Memory used [KB]: 10746
% 1.31/0.54  % (10357)Time elapsed: 0.127 s
% 1.31/0.54  % (10357)------------------------------
% 1.31/0.54  % (10357)------------------------------
% 1.31/0.54  % (10335)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.54  % (10361)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.55  % (10350)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.55  % (10336)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.55  % (10363)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (10351)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.55  % (10353)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.55  % (10364)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (10355)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.55  % (10342)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.56  % (10359)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.56  % (10345)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.56  % (10352)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.56  % (10356)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.56  % (10360)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.56  % (10343)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.57  % (10358)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.57  % (10344)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.57  % (10341)Refutation found. Thanks to Tanya!
% 1.31/0.57  % SZS status Theorem for theBenchmark
% 1.31/0.57  % SZS output start Proof for theBenchmark
% 1.31/0.57  fof(f673,plain,(
% 1.31/0.57    $false),
% 1.31/0.57    inference(subsumption_resolution,[],[f657,f201])).
% 1.31/0.57  fof(f201,plain,(
% 1.31/0.57    k1_xboole_0 != sK1),
% 1.31/0.57    inference(resolution,[],[f192,f80])).
% 1.31/0.57  fof(f80,plain,(
% 1.31/0.57    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | k1_xboole_0 != sK1),
% 1.31/0.57    inference(inner_rewriting,[],[f64])).
% 1.31/0.57  fof(f64,plain,(
% 1.31/0.57    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.31/0.57    inference(definition_unfolding,[],[f28,f31])).
% 1.31/0.57  fof(f31,plain,(
% 1.31/0.57    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f13])).
% 1.31/0.57  fof(f13,axiom,(
% 1.31/0.57    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.31/0.57  fof(f28,plain,(
% 1.31/0.57    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.31/0.57    inference(cnf_transformation,[],[f19])).
% 1.31/0.57  fof(f19,plain,(
% 1.31/0.57    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f17])).
% 1.31/0.57  fof(f17,negated_conjecture,(
% 1.31/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.31/0.57    inference(negated_conjecture,[],[f16])).
% 1.31/0.57  fof(f16,conjecture,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).
% 1.31/0.57  fof(f192,plain,(
% 1.31/0.57    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.31/0.57    inference(forward_demodulation,[],[f180,f177])).
% 1.31/0.57  fof(f177,plain,(
% 1.31/0.57    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 1.31/0.57    inference(resolution,[],[f174,f32])).
% 1.31/0.57  fof(f32,plain,(
% 1.31/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f20])).
% 1.31/0.57  fof(f20,plain,(
% 1.31/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.31/0.57    inference(ennf_transformation,[],[f4])).
% 1.31/0.57  fof(f4,axiom,(
% 1.31/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.31/0.57  fof(f174,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,sK1))) )),
% 1.31/0.57    inference(subsumption_resolution,[],[f169,f145])).
% 1.31/0.57  fof(f145,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1)) | ~r2_hidden(X0,X1)) )),
% 1.31/0.57    inference(resolution,[],[f144,f39])).
% 1.31/0.57  fof(f39,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f22])).
% 1.31/0.57  fof(f22,plain,(
% 1.31/0.57    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.57    inference(ennf_transformation,[],[f18])).
% 1.31/0.57  fof(f18,plain,(
% 1.31/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.57    inference(rectify,[],[f3])).
% 1.31/0.57  fof(f3,axiom,(
% 1.31/0.57    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.31/0.57  fof(f144,plain,(
% 1.31/0.57    ( ! [X6] : (r1_xboole_0(X6,k4_xboole_0(X6,X6))) )),
% 1.31/0.57    inference(trivial_inequality_removal,[],[f143])).
% 1.31/0.57  fof(f143,plain,(
% 1.31/0.57    ( ! [X6] : (X6 != X6 | r1_xboole_0(X6,k4_xboole_0(X6,X6))) )),
% 1.31/0.57    inference(superposition,[],[f50,f111])).
% 1.31/0.57  fof(f111,plain,(
% 1.31/0.57    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.31/0.57    inference(resolution,[],[f66,f73])).
% 1.31/0.57  fof(f73,plain,(
% 1.31/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.57    inference(equality_resolution,[],[f45])).
% 1.31/0.57  fof(f45,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f5])).
% 1.31/0.57  fof(f5,axiom,(
% 1.31/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.57  fof(f66,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.31/0.57    inference(definition_unfolding,[],[f42,f33])).
% 1.31/0.57  fof(f33,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f8])).
% 1.31/0.57  fof(f8,axiom,(
% 1.31/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.31/0.57  fof(f42,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f23])).
% 1.31/0.57  fof(f23,plain,(
% 1.31/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.31/0.57    inference(ennf_transformation,[],[f7])).
% 1.31/0.57  fof(f7,axiom,(
% 1.31/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.31/0.57  fof(f50,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f9])).
% 1.31/0.57  fof(f9,axiom,(
% 1.31/0.57    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.31/0.57  fof(f169,plain,(
% 1.31/0.57    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK1,sK1)) | r2_hidden(X0,sK1)) )),
% 1.31/0.57    inference(superposition,[],[f79,f113])).
% 1.31/0.57  fof(f113,plain,(
% 1.31/0.57    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.31/0.57    inference(resolution,[],[f66,f87])).
% 1.31/0.57  fof(f87,plain,(
% 1.31/0.57    r1_tarski(sK1,sK0)),
% 1.31/0.57    inference(resolution,[],[f86,f75])).
% 1.31/0.57  fof(f75,plain,(
% 1.31/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.31/0.57    inference(equality_resolution,[],[f53])).
% 1.31/0.57  fof(f53,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.31/0.57    inference(cnf_transformation,[],[f11])).
% 1.31/0.57  fof(f11,axiom,(
% 1.31/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.31/0.57  fof(f86,plain,(
% 1.31/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.31/0.57    inference(subsumption_resolution,[],[f83,f30])).
% 1.31/0.57  fof(f30,plain,(
% 1.31/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f15])).
% 1.31/0.57  fof(f15,axiom,(
% 1.31/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.31/0.57  fof(f83,plain,(
% 1.31/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.31/0.57    inference(resolution,[],[f38,f29])).
% 1.31/0.57  fof(f29,plain,(
% 1.31/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.31/0.57    inference(cnf_transformation,[],[f19])).
% 1.31/0.57  fof(f38,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f21])).
% 1.31/0.57  fof(f21,plain,(
% 1.31/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f12])).
% 1.31/0.57  fof(f12,axiom,(
% 1.31/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.31/0.57  fof(f79,plain,(
% 1.31/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.31/0.57    inference(equality_resolution,[],[f69])).
% 1.31/0.57  fof(f69,plain,(
% 1.31/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.31/0.57    inference(definition_unfolding,[],[f60,f33])).
% 1.31/0.57  fof(f60,plain,(
% 1.31/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.31/0.57    inference(cnf_transformation,[],[f2])).
% 1.31/0.57  fof(f2,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.31/0.57  fof(f180,plain,(
% 1.31/0.57    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,sK1),X2)) )),
% 1.31/0.57    inference(resolution,[],[f174,f48])).
% 1.31/0.57  fof(f48,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f25])).
% 1.31/0.57  fof(f25,plain,(
% 1.31/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f1])).
% 1.31/0.57  fof(f1,axiom,(
% 1.31/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.31/0.57  fof(f657,plain,(
% 1.31/0.57    k1_xboole_0 = sK1),
% 1.31/0.57    inference(superposition,[],[f512,f388])).
% 1.31/0.57  fof(f388,plain,(
% 1.31/0.57    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 1.31/0.57    inference(forward_demodulation,[],[f358,f360])).
% 1.31/0.57  fof(f360,plain,(
% 1.31/0.57    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 1.31/0.57    inference(forward_demodulation,[],[f350,f200])).
% 1.31/0.57  fof(f200,plain,(
% 1.31/0.57    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.31/0.57    inference(resolution,[],[f191,f51])).
% 1.31/0.57  fof(f51,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.31/0.57    inference(cnf_transformation,[],[f9])).
% 1.31/0.57  fof(f191,plain,(
% 1.31/0.57    ( ! [X1] : (r1_xboole_0(X1,k1_xboole_0)) )),
% 1.31/0.57    inference(forward_demodulation,[],[f179,f177])).
% 1.31/0.57  fof(f179,plain,(
% 1.31/0.57    ( ! [X1] : (r1_xboole_0(X1,k4_xboole_0(sK1,sK1))) )),
% 1.31/0.57    inference(resolution,[],[f174,f41])).
% 1.31/0.57  fof(f41,plain,(
% 1.31/0.57    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f22])).
% 1.31/0.57  fof(f350,plain,(
% 1.31/0.57    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.31/0.57    inference(superposition,[],[f63,f250])).
% 1.31/0.57  fof(f250,plain,(
% 1.31/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.31/0.57    inference(resolution,[],[f176,f32])).
% 1.31/0.57  fof(f176,plain,(
% 1.31/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(X2,X2))) )),
% 1.31/0.57    inference(subsumption_resolution,[],[f171,f145])).
% 1.31/0.57  fof(f171,plain,(
% 1.31/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(X2,X2)) | r2_hidden(X3,X2)) )),
% 1.31/0.57    inference(superposition,[],[f79,f111])).
% 1.31/0.57  fof(f63,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.31/0.57    inference(definition_unfolding,[],[f34,f33])).
% 1.31/0.57  fof(f34,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.31/0.57    inference(cnf_transformation,[],[f6])).
% 1.31/0.57  fof(f6,axiom,(
% 1.31/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.31/0.57  fof(f358,plain,(
% 1.31/0.57    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,sK1)),
% 1.31/0.57    inference(superposition,[],[f63,f301])).
% 1.31/0.57  fof(f301,plain,(
% 1.31/0.57    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 1.31/0.57    inference(subsumption_resolution,[],[f294,f201])).
% 1.31/0.57  fof(f294,plain,(
% 1.31/0.57    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | k1_xboole_0 = sK1),
% 1.31/0.57    inference(backward_demodulation,[],[f112,f288])).
% 1.31/0.57  fof(f288,plain,(
% 1.31/0.57    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.31/0.57    inference(resolution,[],[f43,f29])).
% 1.31/0.57  fof(f43,plain,(
% 1.31/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f24])).
% 1.31/0.57  fof(f24,plain,(
% 1.31/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.31/0.57    inference(ennf_transformation,[],[f14])).
% 1.31/0.57  fof(f14,axiom,(
% 1.31/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.31/0.57  fof(f112,plain,(
% 1.31/0.57    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) | k1_xboole_0 = sK1),
% 1.31/0.57    inference(resolution,[],[f66,f65])).
% 1.31/0.57  fof(f65,plain,(
% 1.31/0.57    r1_tarski(sK1,k3_subset_1(sK0,sK1)) | k1_xboole_0 = sK1),
% 1.31/0.57    inference(definition_unfolding,[],[f27,f31])).
% 1.31/0.57  fof(f27,plain,(
% 1.31/0.57    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 1.31/0.57    inference(cnf_transformation,[],[f19])).
% 1.31/0.57  fof(f512,plain,(
% 1.31/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.31/0.57    inference(resolution,[],[f94,f73])).
% 1.31/0.57  fof(f94,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X2,X1)) = X0) )),
% 1.31/0.57    inference(resolution,[],[f56,f51])).
% 1.31/0.57  fof(f56,plain,(
% 1.31/0.57    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.31/0.57    inference(cnf_transformation,[],[f26])).
% 1.31/0.57  fof(f26,plain,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.31/0.57    inference(ennf_transformation,[],[f10])).
% 1.31/0.57  fof(f10,axiom,(
% 1.31/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 1.31/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 1.31/0.57  % SZS output end Proof for theBenchmark
% 1.31/0.57  % (10341)------------------------------
% 1.31/0.57  % (10341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.57  % (10341)Termination reason: Refutation
% 1.31/0.57  
% 1.31/0.57  % (10341)Memory used [KB]: 6524
% 1.31/0.57  % (10341)Time elapsed: 0.161 s
% 1.31/0.57  % (10341)------------------------------
% 1.31/0.57  % (10341)------------------------------
% 1.31/0.59  % (10334)Success in time 0.232 s
%------------------------------------------------------------------------------
