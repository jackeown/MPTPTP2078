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
% DateTime   : Thu Dec  3 12:46:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 106 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :   18
%              Number of atoms          :  132 ( 294 expanded)
%              Number of equality atoms :   52 (  73 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f656,plain,(
    $false ),
    inference(subsumption_resolution,[],[f655,f237])).

% (8615)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f237,plain,(
    r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f179,f33])).

% (8623)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f179,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4)))
      | r1_tarski(k8_setfam_1(X4,X3),X4) ) ),
    inference(resolution,[],[f45,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f655,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f562,f61])).

fof(f61,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f58,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f562,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f35,f560])).

fof(f560,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f534,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f48,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f534,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f479,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f56,f38])).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f479,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f34,f477])).

fof(f477,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f476,f34])).

fof(f476,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f475])).

fof(f475,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f431,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f431,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f402,f397])).

fof(f397,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f388,f158])).

fof(f158,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f44,f36])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f388,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f47,f36])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f402,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f35,f396])).

fof(f396,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f387,f157])).

fof(f157,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f44,f33])).

fof(f387,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f47,f33])).

fof(f34,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f35,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:03:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8600)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (8606)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (8616)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (8609)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (8598)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (8597)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8599)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (8619)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (8596)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8617)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (8600)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (8594)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f656,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f655,f237])).
% 0.21/0.54  % (8615)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.21/0.54    inference(resolution,[],[f179,f33])).
% 0.21/0.54  % (8623)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(flattening,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f16])).
% 0.21/0.54  fof(f16,conjecture,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X4))) | r1_tarski(k8_setfam_1(X4,X3),X4)) )),
% 0.21/0.54    inference(resolution,[],[f45,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.54  fof(f655,plain,(
% 0.21/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 0.21/0.54    inference(forward_demodulation,[],[f562,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f58,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.54  fof(f562,plain,(
% 0.21/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 0.21/0.54    inference(backward_demodulation,[],[f35,f560])).
% 0.21/0.54  fof(f560,plain,(
% 0.21/0.54    k1_xboole_0 = sK1),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f537])).
% 0.21/0.54  fof(f537,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(resolution,[],[f534,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.21/0.54  fof(f534,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(sK1,X0) | k1_xboole_0 = sK1) )),
% 0.21/0.54    inference(resolution,[],[f479,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f56,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.54  fof(f479,plain,(
% 0.21/0.54    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(superposition,[],[f34,f477])).
% 0.21/0.54  fof(f477,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(subsumption_resolution,[],[f476,f34])).
% 0.21/0.54  fof(f476,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f475])).
% 0.21/0.54  fof(f475,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(resolution,[],[f431,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.54  fof(f431,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.21/0.54    inference(superposition,[],[f402,f397])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 0.21/0.54    inference(forward_demodulation,[],[f388,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.54    inference(resolution,[],[f44,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 0.21/0.54    inference(resolution,[],[f47,f36])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f402,plain,(
% 0.21/0.54    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(superposition,[],[f35,f396])).
% 0.21/0.54  fof(f396,plain,(
% 0.21/0.54    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 0.21/0.54    inference(forward_demodulation,[],[f387,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.54    inference(resolution,[],[f44,f33])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 0.21/0.54    inference(resolution,[],[f47,f33])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    r1_tarski(sK1,sK2)),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (8600)------------------------------
% 0.21/0.54  % (8600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8600)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (8600)Memory used [KB]: 6524
% 0.21/0.54  % (8600)Time elapsed: 0.106 s
% 0.21/0.54  % (8600)------------------------------
% 0.21/0.54  % (8600)------------------------------
% 0.21/0.54  % (8593)Success in time 0.182 s
%------------------------------------------------------------------------------
