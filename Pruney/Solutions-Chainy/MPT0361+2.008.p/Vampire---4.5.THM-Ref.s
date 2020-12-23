%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:59 EST 2020

% Result     : Theorem 2.47s
% Output     : Refutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 190 expanded)
%              Number of leaves         :   15 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  149 ( 391 expanded)
%              Number of equality atoms :   45 (  91 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3404,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3403,f696])).

fof(f696,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f32,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3403,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f2325,f3395])).

fof(f3395,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f3269,f2656])).

fof(f2656,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(resolution,[],[f685,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f685,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(subsumption_resolution,[],[f683,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f683,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f40,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3269,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f3268,f69])).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3268,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK0)) ),
    inference(forward_demodulation,[],[f3109,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f3109,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k1_xboole_0)) ),
    inference(superposition,[],[f1176,f2953])).

fof(f2953,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f2660,f2952])).

fof(f2952,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    inference(forward_demodulation,[],[f2848,f2764])).

fof(f2764,plain,(
    ! [X1] : k3_subset_1(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f2661,f104])).

fof(f104,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f100,f69])).

fof(f100,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2661,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = k3_subset_1(X1,k1_xboole_0) ),
    inference(resolution,[],[f2656,f30])).

fof(f2848,plain,(
    ! [X1] : k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0)) ),
    inference(resolution,[],[f2841,f30])).

fof(f2841,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(resolution,[],[f691,f55])).

fof(f691,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f688,f29])).

fof(f688,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ r2_hidden(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f41,f37])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2660,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f2656,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1176,plain,(
    ! [X0] : r1_tarski(X0,k2_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f1171,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1171,plain,(
    ! [X13] : r1_tarski(k4_xboole_0(X13,sK0),k4_xboole_0(X13,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1150,f33])).

fof(f1150,plain,(
    ! [X13] : r1_tarski(k4_xboole_0(X13,sK0),k4_xboole_0(X13,k2_xboole_0(sK2,sK1))) ),
    inference(superposition,[],[f763,f74])).

fof(f74,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f39,f67])).

fof(f67,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f65,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f65,plain,(
    r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f61,f29])).

fof(f61,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f763,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,sK0)),k4_xboole_0(X0,k2_xboole_0(X1,sK1))) ),
    inference(forward_demodulation,[],[f760,f49])).

fof(f760,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,sK0)),k4_xboole_0(k4_xboole_0(X0,X1),sK1)) ),
    inference(superposition,[],[f741,f49])).

fof(f741,plain,(
    ! [X37] : r1_tarski(k4_xboole_0(X37,sK0),k4_xboole_0(X37,sK1)) ),
    inference(superposition,[],[f696,f75])).

fof(f75,plain,(
    sK0 = k2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f39,f68])).

fof(f68,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f66,f54])).

fof(f66,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f62,f29])).

fof(f62,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f38,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f2325,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f684,f2322])).

fof(f2322,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f1789,f28])).

fof(f1789,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2) ) ),
    inference(resolution,[],[f51,f26])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f684,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f27,f682])).

fof(f682,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f40,f28])).

fof(f27,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:50:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (16342)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.47  % (16350)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.47  % (16338)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.48  % (16339)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.49  % (16354)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.49  % (16352)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.49  % (16344)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % (16332)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (16336)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.50  % (16331)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.50  % (16334)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (16331)Refutation not found, incomplete strategy% (16331)------------------------------
% 0.19/0.50  % (16331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (16331)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (16331)Memory used [KB]: 10618
% 0.19/0.50  % (16331)Time elapsed: 0.106 s
% 0.19/0.50  % (16331)------------------------------
% 0.19/0.50  % (16331)------------------------------
% 0.19/0.50  % (16355)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.50  % (16336)Refutation not found, incomplete strategy% (16336)------------------------------
% 0.19/0.50  % (16336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (16336)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (16336)Memory used [KB]: 10618
% 0.19/0.50  % (16336)Time elapsed: 0.069 s
% 0.19/0.50  % (16336)------------------------------
% 0.19/0.50  % (16336)------------------------------
% 0.19/0.51  % (16335)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.51  % (16335)Refutation not found, incomplete strategy% (16335)------------------------------
% 0.19/0.51  % (16335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (16335)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (16335)Memory used [KB]: 6140
% 0.19/0.51  % (16335)Time elapsed: 0.117 s
% 0.19/0.51  % (16335)------------------------------
% 0.19/0.51  % (16335)------------------------------
% 0.19/0.51  % (16340)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.51  % (16349)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.51  % (16330)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (16351)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.51  % (16333)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.51  % (16347)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.52  % (16343)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.52  % (16341)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.52  % (16345)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.52  % (16343)Refutation not found, incomplete strategy% (16343)------------------------------
% 0.19/0.52  % (16343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (16343)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (16343)Memory used [KB]: 6140
% 0.19/0.52  % (16343)Time elapsed: 0.129 s
% 0.19/0.52  % (16343)------------------------------
% 0.19/0.52  % (16343)------------------------------
% 0.19/0.52  % (16341)Refutation not found, incomplete strategy% (16341)------------------------------
% 0.19/0.52  % (16341)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (16341)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (16341)Memory used [KB]: 10618
% 0.19/0.52  % (16341)Time elapsed: 0.131 s
% 0.19/0.52  % (16341)------------------------------
% 0.19/0.52  % (16341)------------------------------
% 0.19/0.52  % (16337)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.53  % (16346)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.53  % (16353)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.53  % (16348)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.66/0.60  % (16339)Refutation not found, incomplete strategy% (16339)------------------------------
% 1.66/0.60  % (16339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.60  % (16339)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.60  
% 1.66/0.60  % (16339)Memory used [KB]: 6140
% 1.66/0.60  % (16339)Time elapsed: 0.180 s
% 1.66/0.60  % (16339)------------------------------
% 1.66/0.60  % (16339)------------------------------
% 2.47/0.67  % (16349)Refutation found. Thanks to Tanya!
% 2.47/0.67  % SZS status Theorem for theBenchmark
% 2.47/0.67  % SZS output start Proof for theBenchmark
% 2.47/0.67  fof(f3404,plain,(
% 2.47/0.67    $false),
% 2.47/0.67    inference(subsumption_resolution,[],[f3403,f696])).
% 2.47/0.67  fof(f696,plain,(
% 2.47/0.67    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 2.47/0.67    inference(superposition,[],[f32,f49])).
% 2.47/0.67  fof(f49,plain,(
% 2.47/0.67    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.47/0.67    inference(cnf_transformation,[],[f7])).
% 2.47/0.67  fof(f7,axiom,(
% 2.47/0.67    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.47/0.67  fof(f32,plain,(
% 2.47/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f5])).
% 2.47/0.67  fof(f5,axiom,(
% 2.47/0.67    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.47/0.67  fof(f3403,plain,(
% 2.47/0.67    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.47/0.67    inference(backward_demodulation,[],[f2325,f3395])).
% 2.47/0.67  fof(f3395,plain,(
% 2.47/0.67    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(sK0,k2_xboole_0(sK1,sK2))),
% 2.47/0.67    inference(resolution,[],[f3269,f2656])).
% 2.47/0.67  fof(f2656,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.47/0.67    inference(resolution,[],[f685,f55])).
% 2.47/0.67  fof(f55,plain,(
% 2.47/0.67    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 2.47/0.67    inference(equality_resolution,[],[f45])).
% 2.47/0.67  fof(f45,plain,(
% 2.47/0.67    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.47/0.67    inference(cnf_transformation,[],[f10])).
% 2.47/0.67  fof(f10,axiom,(
% 2.47/0.67    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.47/0.67  fof(f685,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.47/0.67    inference(subsumption_resolution,[],[f683,f29])).
% 2.47/0.67  fof(f29,plain,(
% 2.47/0.67    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.47/0.67    inference(cnf_transformation,[],[f13])).
% 2.47/0.67  fof(f13,axiom,(
% 2.47/0.67    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.47/0.67  fof(f683,plain,(
% 2.47/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~r2_hidden(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.47/0.67    inference(resolution,[],[f40,f37])).
% 2.47/0.67  fof(f37,plain,(
% 2.47/0.67    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f19])).
% 2.47/0.67  fof(f19,plain,(
% 2.47/0.67    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.47/0.67    inference(ennf_transformation,[],[f11])).
% 2.47/0.67  fof(f11,axiom,(
% 2.47/0.67    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.47/0.67  fof(f40,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f21])).
% 2.47/0.67  fof(f21,plain,(
% 2.47/0.67    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.47/0.67    inference(ennf_transformation,[],[f12])).
% 2.47/0.67  fof(f12,axiom,(
% 2.47/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.47/0.67  fof(f3269,plain,(
% 2.47/0.67    r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 2.47/0.67    inference(forward_demodulation,[],[f3268,f69])).
% 2.47/0.67  fof(f69,plain,(
% 2.47/0.67    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.47/0.67    inference(resolution,[],[f39,f30])).
% 2.47/0.67  fof(f30,plain,(
% 2.47/0.67    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f4])).
% 2.47/0.67  fof(f4,axiom,(
% 2.47/0.67    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.47/0.67  fof(f39,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.47/0.67    inference(cnf_transformation,[],[f20])).
% 2.47/0.67  fof(f20,plain,(
% 2.47/0.67    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.47/0.67    inference(ennf_transformation,[],[f3])).
% 2.47/0.67  fof(f3,axiom,(
% 2.47/0.67    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.47/0.67  fof(f3268,plain,(
% 2.47/0.67    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(k1_xboole_0,sK0))),
% 2.47/0.67    inference(forward_demodulation,[],[f3109,f33])).
% 2.47/0.67  fof(f33,plain,(
% 2.47/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f1])).
% 2.47/0.67  fof(f1,axiom,(
% 2.47/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.47/0.67  fof(f3109,plain,(
% 2.47/0.67    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK0,k1_xboole_0))),
% 2.47/0.67    inference(superposition,[],[f1176,f2953])).
% 2.47/0.67  fof(f2953,plain,(
% 2.47/0.67    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.47/0.67    inference(backward_demodulation,[],[f2660,f2952])).
% 2.47/0.67  fof(f2952,plain,(
% 2.47/0.67    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) )),
% 2.47/0.67    inference(forward_demodulation,[],[f2848,f2764])).
% 2.47/0.67  fof(f2764,plain,(
% 2.47/0.67    ( ! [X1] : (k3_subset_1(X1,k1_xboole_0) = X1) )),
% 2.47/0.67    inference(forward_demodulation,[],[f2661,f104])).
% 2.47/0.67  fof(f104,plain,(
% 2.47/0.67    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 2.47/0.67    inference(forward_demodulation,[],[f100,f69])).
% 2.47/0.67  fof(f100,plain,(
% 2.47/0.67    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 2.47/0.67    inference(superposition,[],[f34,f69])).
% 2.47/0.67  fof(f34,plain,(
% 2.47/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.47/0.67    inference(cnf_transformation,[],[f6])).
% 2.47/0.67  fof(f6,axiom,(
% 2.47/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.47/0.67  fof(f2661,plain,(
% 2.47/0.67    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = k3_subset_1(X1,k1_xboole_0)) )),
% 2.47/0.67    inference(resolution,[],[f2656,f30])).
% 2.47/0.67  fof(f2848,plain,(
% 2.47/0.67    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,k3_subset_1(X1,k1_xboole_0))) )),
% 2.47/0.67    inference(resolution,[],[f2841,f30])).
% 2.47/0.67  fof(f2841,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.47/0.67    inference(resolution,[],[f691,f55])).
% 2.47/0.67  fof(f691,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.47/0.67    inference(subsumption_resolution,[],[f688,f29])).
% 2.47/0.67  fof(f688,plain,(
% 2.47/0.67    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~r2_hidden(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.47/0.67    inference(resolution,[],[f41,f37])).
% 2.47/0.67  fof(f41,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.47/0.67    inference(cnf_transformation,[],[f22])).
% 2.47/0.67  fof(f22,plain,(
% 2.47/0.67    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.47/0.67    inference(ennf_transformation,[],[f14])).
% 2.47/0.67  fof(f14,axiom,(
% 2.47/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.47/0.67  fof(f2660,plain,(
% 2.47/0.67    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 2.47/0.67    inference(resolution,[],[f2656,f52])).
% 2.47/0.67  fof(f52,plain,(
% 2.47/0.67    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.47/0.67    inference(equality_resolution,[],[f43])).
% 2.47/0.67  fof(f43,plain,(
% 2.47/0.67    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.47/0.67    inference(cnf_transformation,[],[f2])).
% 2.47/0.67  fof(f2,axiom,(
% 2.47/0.67    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.47/0.67  fof(f1176,plain,(
% 2.47/0.67    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(sK1,sK2))))) )),
% 2.47/0.67    inference(resolution,[],[f1171,f50])).
% 2.47/0.67  fof(f50,plain,(
% 2.47/0.67    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.47/0.67    inference(cnf_transformation,[],[f23])).
% 2.47/0.67  fof(f23,plain,(
% 2.47/0.67    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.47/0.67    inference(ennf_transformation,[],[f8])).
% 2.47/0.67  fof(f8,axiom,(
% 2.47/0.67    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.47/0.67  fof(f1171,plain,(
% 2.47/0.67    ( ! [X13] : (r1_tarski(k4_xboole_0(X13,sK0),k4_xboole_0(X13,k2_xboole_0(sK1,sK2)))) )),
% 2.47/0.67    inference(forward_demodulation,[],[f1150,f33])).
% 2.47/0.67  fof(f1150,plain,(
% 2.47/0.67    ( ! [X13] : (r1_tarski(k4_xboole_0(X13,sK0),k4_xboole_0(X13,k2_xboole_0(sK2,sK1)))) )),
% 2.47/0.67    inference(superposition,[],[f763,f74])).
% 2.47/0.67  fof(f74,plain,(
% 2.47/0.67    sK0 = k2_xboole_0(sK2,sK0)),
% 2.47/0.67    inference(resolution,[],[f39,f67])).
% 2.47/0.67  fof(f67,plain,(
% 2.47/0.67    r1_tarski(sK2,sK0)),
% 2.47/0.67    inference(resolution,[],[f65,f54])).
% 2.47/0.67  fof(f54,plain,(
% 2.47/0.67    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 2.47/0.67    inference(equality_resolution,[],[f46])).
% 2.47/0.67  fof(f46,plain,(
% 2.47/0.67    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.47/0.67    inference(cnf_transformation,[],[f10])).
% 2.47/0.67  fof(f65,plain,(
% 2.47/0.67    r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 2.47/0.67    inference(subsumption_resolution,[],[f61,f29])).
% 2.47/0.67  fof(f61,plain,(
% 2.47/0.67    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.47/0.67    inference(resolution,[],[f38,f26])).
% 2.47/0.67  fof(f26,plain,(
% 2.47/0.67    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.47/0.67    inference(cnf_transformation,[],[f18])).
% 2.47/0.67  fof(f18,plain,(
% 2.47/0.67    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.47/0.67    inference(ennf_transformation,[],[f17])).
% 2.47/0.67  fof(f17,negated_conjecture,(
% 2.47/0.67    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.47/0.67    inference(negated_conjecture,[],[f16])).
% 2.47/0.67  fof(f16,conjecture,(
% 2.47/0.67    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 2.47/0.67  fof(f38,plain,(
% 2.47/0.67    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f19])).
% 2.47/0.67  fof(f763,plain,(
% 2.47/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,sK0)),k4_xboole_0(X0,k2_xboole_0(X1,sK1)))) )),
% 2.47/0.67    inference(forward_demodulation,[],[f760,f49])).
% 2.47/0.67  fof(f760,plain,(
% 2.47/0.67    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,sK0)),k4_xboole_0(k4_xboole_0(X0,X1),sK1))) )),
% 2.47/0.67    inference(superposition,[],[f741,f49])).
% 2.47/0.67  fof(f741,plain,(
% 2.47/0.67    ( ! [X37] : (r1_tarski(k4_xboole_0(X37,sK0),k4_xboole_0(X37,sK1))) )),
% 2.47/0.67    inference(superposition,[],[f696,f75])).
% 2.47/0.67  fof(f75,plain,(
% 2.47/0.67    sK0 = k2_xboole_0(sK1,sK0)),
% 2.47/0.67    inference(resolution,[],[f39,f68])).
% 2.47/0.67  fof(f68,plain,(
% 2.47/0.67    r1_tarski(sK1,sK0)),
% 2.47/0.67    inference(resolution,[],[f66,f54])).
% 2.47/0.67  fof(f66,plain,(
% 2.47/0.67    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 2.47/0.67    inference(subsumption_resolution,[],[f62,f29])).
% 2.47/0.67  fof(f62,plain,(
% 2.47/0.67    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 2.47/0.67    inference(resolution,[],[f38,f28])).
% 2.47/0.67  fof(f28,plain,(
% 2.47/0.67    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.47/0.67    inference(cnf_transformation,[],[f18])).
% 2.47/0.67  fof(f2325,plain,(
% 2.47/0.67    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.47/0.67    inference(backward_demodulation,[],[f684,f2322])).
% 2.47/0.67  fof(f2322,plain,(
% 2.47/0.67    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 2.47/0.67    inference(resolution,[],[f1789,f28])).
% 2.47/0.67  fof(f1789,plain,(
% 2.47/0.67    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2)) )),
% 2.47/0.67    inference(resolution,[],[f51,f26])).
% 2.47/0.67  fof(f51,plain,(
% 2.47/0.67    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.47/0.67    inference(cnf_transformation,[],[f25])).
% 2.47/0.67  fof(f25,plain,(
% 2.47/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.47/0.67    inference(flattening,[],[f24])).
% 2.47/0.67  fof(f24,plain,(
% 2.47/0.67    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.47/0.67    inference(ennf_transformation,[],[f15])).
% 2.47/0.67  fof(f15,axiom,(
% 2.47/0.67    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.47/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.47/0.67  fof(f684,plain,(
% 2.47/0.67    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 2.47/0.67    inference(backward_demodulation,[],[f27,f682])).
% 2.47/0.67  fof(f682,plain,(
% 2.47/0.67    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 2.47/0.67    inference(resolution,[],[f40,f28])).
% 2.47/0.67  fof(f27,plain,(
% 2.47/0.67    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 2.47/0.67    inference(cnf_transformation,[],[f18])).
% 2.47/0.67  % SZS output end Proof for theBenchmark
% 2.47/0.67  % (16349)------------------------------
% 2.47/0.67  % (16349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.47/0.67  % (16349)Termination reason: Refutation
% 2.47/0.67  
% 2.47/0.67  % (16349)Memory used [KB]: 4093
% 2.47/0.67  % (16349)Time elapsed: 0.286 s
% 2.47/0.67  % (16349)------------------------------
% 2.47/0.67  % (16349)------------------------------
% 2.47/0.67  % (16329)Success in time 0.318 s
%------------------------------------------------------------------------------
