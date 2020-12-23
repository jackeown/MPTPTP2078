%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:48 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 234 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   18
%              Number of atoms          :  121 ( 483 expanded)
%              Number of equality atoms :   42 ( 160 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(subsumption_resolution,[],[f348,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

fof(f348,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f347,f148])).

fof(f148,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f144,f62])).

fof(f62,plain,(
    sK1 = k3_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f39,f27])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f144,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f53,f27])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f347,plain,(
    sK1 = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f345,f315])).

fof(f315,plain,(
    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f63,f310])).

fof(f310,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f220,f296])).

fof(f296,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f294,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f294,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f291,f39])).

fof(f291,plain,(
    r1_tarski(sK2,sK0) ),
    inference(forward_demodulation,[],[f290,f48])).

fof(f48,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f290,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f289,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f289,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2))
    | r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f286,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f286,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r1_tarski(X0,k3_subset_1(sK0,sK2))
      | r1_tarski(sK2,k3_subset_1(sK0,X0)) ) ),
    inference(resolution,[],[f41,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f220,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f49,f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f38])).

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

fof(f63,plain,(
    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f39,f28])).

fof(f28,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f345,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))) ),
    inference(resolution,[],[f339,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f339,plain,(
    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f329,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,X0)
      | r1_xboole_0(sK1,X0) ) ),
    inference(resolution,[],[f46,f27])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f329,plain,(
    r1_xboole_0(sK2,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f313,f310])).

fof(f313,plain,(
    r1_xboole_0(sK2,k3_subset_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f308,f296])).

fof(f308,plain,(
    r1_xboole_0(k3_xboole_0(sK0,sK2),k3_subset_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f260,f296])).

fof(f260,plain,(
    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_subset_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f258,f36])).

fof(f258,plain,(
    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),sK0),k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f54,f220])).

fof(f54,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:23:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 1.20/0.51  % (6475)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.51  % (6468)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.20/0.51  % (6458)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.51  % (6468)Refutation not found, incomplete strategy% (6468)------------------------------
% 1.20/0.51  % (6468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.51  % (6468)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.51  
% 1.20/0.51  % (6468)Memory used [KB]: 6140
% 1.20/0.51  % (6468)Time elapsed: 0.003 s
% 1.20/0.51  % (6468)------------------------------
% 1.20/0.51  % (6468)------------------------------
% 1.20/0.52  % (6464)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.52  % (6475)Refutation not found, incomplete strategy% (6475)------------------------------
% 1.20/0.52  % (6475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (6475)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (6475)Memory used [KB]: 10618
% 1.20/0.52  % (6475)Time elapsed: 0.059 s
% 1.20/0.52  % (6475)------------------------------
% 1.20/0.52  % (6475)------------------------------
% 1.20/0.52  % (6457)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.52  % (6456)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.20/0.52  % (6458)Refutation found. Thanks to Tanya!
% 1.20/0.52  % SZS status Theorem for theBenchmark
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f349,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(subsumption_resolution,[],[f348,f29])).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    k1_xboole_0 != sK1),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.20/0.52    inference(flattening,[],[f18])).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.20/0.52    inference(ennf_transformation,[],[f17])).
% 1.20/0.52  fof(f17,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.20/0.52    inference(negated_conjecture,[],[f16])).
% 1.20/0.52  fof(f16,conjecture,(
% 1.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).
% 1.20/0.52  fof(f348,plain,(
% 1.20/0.52    k1_xboole_0 = sK1),
% 1.20/0.52    inference(forward_demodulation,[],[f347,f148])).
% 1.20/0.52  fof(f148,plain,(
% 1.20/0.52    k1_xboole_0 = k5_xboole_0(sK1,sK1)),
% 1.20/0.52    inference(forward_demodulation,[],[f144,f62])).
% 1.20/0.52  fof(f62,plain,(
% 1.20/0.52    sK1 = k3_xboole_0(sK1,sK2)),
% 1.20/0.52    inference(resolution,[],[f39,f27])).
% 1.20/0.52  fof(f27,plain,(
% 1.20/0.52    r1_tarski(sK1,sK2)),
% 1.20/0.52    inference(cnf_transformation,[],[f19])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f20])).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.20/0.52  fof(f144,plain,(
% 1.20/0.52    k1_xboole_0 = k5_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.20/0.52    inference(resolution,[],[f53,f27])).
% 1.20/0.52  fof(f53,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(definition_unfolding,[],[f44,f38])).
% 1.20/0.52  fof(f38,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f5])).
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.20/0.52  fof(f44,plain,(
% 1.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.20/0.52  fof(f347,plain,(
% 1.20/0.52    sK1 = k5_xboole_0(sK1,sK1)),
% 1.20/0.52    inference(forward_demodulation,[],[f345,f315])).
% 1.20/0.52  fof(f315,plain,(
% 1.20/0.52    sK1 = k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 1.20/0.52    inference(backward_demodulation,[],[f63,f310])).
% 1.20/0.52  fof(f310,plain,(
% 1.20/0.52    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.20/0.52    inference(backward_demodulation,[],[f220,f296])).
% 1.20/0.52  fof(f296,plain,(
% 1.20/0.52    sK2 = k3_xboole_0(sK0,sK2)),
% 1.20/0.52    inference(superposition,[],[f294,f36])).
% 1.20/0.52  fof(f36,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.20/0.52  fof(f294,plain,(
% 1.20/0.52    sK2 = k3_xboole_0(sK2,sK0)),
% 1.20/0.52    inference(resolution,[],[f291,f39])).
% 1.20/0.52  fof(f291,plain,(
% 1.20/0.52    r1_tarski(sK2,sK0)),
% 1.20/0.52    inference(forward_demodulation,[],[f290,f48])).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.20/0.52    inference(definition_unfolding,[],[f32,f47])).
% 1.20/0.52  fof(f47,plain,(
% 1.20/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.20/0.52    inference(definition_unfolding,[],[f34,f31])).
% 1.20/0.52  fof(f31,plain,(
% 1.20/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f10])).
% 1.20/0.52  fof(f10,axiom,(
% 1.20/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.20/0.52  fof(f34,plain,(
% 1.20/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,axiom,(
% 1.20/0.52    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 1.20/0.52  fof(f32,plain,(
% 1.20/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.20/0.52    inference(cnf_transformation,[],[f11])).
% 1.20/0.52  fof(f11,axiom,(
% 1.20/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.20/0.52  fof(f290,plain,(
% 1.20/0.52    r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0))),
% 1.20/0.52    inference(subsumption_resolution,[],[f289,f30])).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.52  fof(f289,plain,(
% 1.35/0.52    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,sK2)) | r1_tarski(sK2,k3_subset_1(sK0,k1_xboole_0))),
% 1.35/0.52    inference(resolution,[],[f286,f33])).
% 1.35/0.52  fof(f33,plain,(
% 1.35/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.35/0.52    inference(cnf_transformation,[],[f15])).
% 1.35/0.52  fof(f15,axiom,(
% 1.35/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.35/0.52  fof(f286,plain,(
% 1.35/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r1_tarski(X0,k3_subset_1(sK0,sK2)) | r1_tarski(sK2,k3_subset_1(sK0,X0))) )),
% 1.35/0.52    inference(resolution,[],[f41,f26])).
% 1.35/0.52  fof(f26,plain,(
% 1.35/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.35/0.52    inference(cnf_transformation,[],[f19])).
% 1.35/0.52  fof(f41,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1))) )),
% 1.35/0.52    inference(cnf_transformation,[],[f23])).
% 1.35/0.52  fof(f23,plain,(
% 1.35/0.52    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.52    inference(flattening,[],[f22])).
% 1.35/0.52  fof(f22,plain,(
% 1.35/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.52    inference(ennf_transformation,[],[f14])).
% 1.35/0.52  fof(f14,axiom,(
% 1.35/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 1.35/0.52  fof(f220,plain,(
% 1.35/0.52    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 1.35/0.52    inference(resolution,[],[f49,f26])).
% 1.35/0.52  fof(f49,plain,(
% 1.35/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.35/0.52    inference(definition_unfolding,[],[f40,f38])).
% 1.35/0.52  fof(f40,plain,(
% 1.35/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f21])).
% 1.35/0.52  fof(f21,plain,(
% 1.35/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.35/0.52    inference(ennf_transformation,[],[f12])).
% 1.35/0.52  fof(f12,axiom,(
% 1.35/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.35/0.52  fof(f63,plain,(
% 1.35/0.52    sK1 = k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.35/0.52    inference(resolution,[],[f39,f28])).
% 1.35/0.52  fof(f28,plain,(
% 1.35/0.52    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 1.35/0.52    inference(cnf_transformation,[],[f19])).
% 1.35/0.52  fof(f345,plain,(
% 1.35/0.52    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)))),
% 1.35/0.52    inference(resolution,[],[f339,f50])).
% 1.35/0.52  fof(f50,plain,(
% 1.35/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.35/0.52    inference(definition_unfolding,[],[f43,f38])).
% 1.35/0.52  fof(f43,plain,(
% 1.35/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f9])).
% 1.35/0.52  fof(f9,axiom,(
% 1.35/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.35/0.52  fof(f339,plain,(
% 1.35/0.52    r1_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 1.35/0.52    inference(resolution,[],[f329,f84])).
% 1.35/0.52  fof(f84,plain,(
% 1.35/0.52    ( ! [X0] : (~r1_xboole_0(sK2,X0) | r1_xboole_0(sK1,X0)) )),
% 1.35/0.52    inference(resolution,[],[f46,f27])).
% 1.35/0.52  fof(f46,plain,(
% 1.35/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.35/0.52    inference(cnf_transformation,[],[f25])).
% 1.35/0.52  fof(f25,plain,(
% 1.35/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.35/0.52    inference(flattening,[],[f24])).
% 1.35/0.52  fof(f24,plain,(
% 1.35/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.35/0.52    inference(ennf_transformation,[],[f8])).
% 1.35/0.52  fof(f8,axiom,(
% 1.35/0.52    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.35/0.52  fof(f329,plain,(
% 1.35/0.52    r1_xboole_0(sK2,k5_xboole_0(sK0,sK2))),
% 1.35/0.52    inference(backward_demodulation,[],[f313,f310])).
% 1.35/0.52  fof(f313,plain,(
% 1.35/0.52    r1_xboole_0(sK2,k3_subset_1(sK0,sK2))),
% 1.35/0.52    inference(forward_demodulation,[],[f308,f296])).
% 1.35/0.52  fof(f308,plain,(
% 1.35/0.52    r1_xboole_0(k3_xboole_0(sK0,sK2),k3_subset_1(sK0,sK2))),
% 1.35/0.52    inference(backward_demodulation,[],[f260,f296])).
% 1.35/0.52  fof(f260,plain,(
% 1.35/0.52    r1_xboole_0(k3_xboole_0(sK0,k3_xboole_0(sK0,sK2)),k3_subset_1(sK0,sK2))),
% 1.35/0.52    inference(forward_demodulation,[],[f258,f36])).
% 1.35/0.52  fof(f258,plain,(
% 1.35/0.52    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK0,sK2),sK0),k3_subset_1(sK0,sK2))),
% 1.35/0.52    inference(superposition,[],[f54,f220])).
% 1.35/0.52  fof(f54,plain,(
% 1.35/0.52    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X1))) )),
% 1.35/0.52    inference(superposition,[],[f37,f36])).
% 1.35/0.52  fof(f37,plain,(
% 1.35/0.52    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.35/0.52    inference(cnf_transformation,[],[f4])).
% 1.35/0.52  fof(f4,axiom,(
% 1.35/0.52    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.35/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.35/0.52  % SZS output end Proof for theBenchmark
% 1.35/0.52  % (6458)------------------------------
% 1.35/0.52  % (6458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.52  % (6458)Termination reason: Refutation
% 1.35/0.52  
% 1.35/0.52  % (6458)Memory used [KB]: 6396
% 1.35/0.52  % (6458)Time elapsed: 0.079 s
% 1.35/0.52  % (6458)------------------------------
% 1.35/0.52  % (6458)------------------------------
% 1.35/0.53  % (6448)Success in time 0.168 s
%------------------------------------------------------------------------------
