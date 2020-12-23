%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:36 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 167 expanded)
%              Number of leaves         :   12 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  175 ( 441 expanded)
%              Number of equality atoms :   61 ( 106 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f250,f125])).

fof(f125,plain,(
    r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(resolution,[],[f121,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

% (28057)Termination reason: Refutation not found, incomplete strategy
fof(f121,plain,(
    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f34,f27])).

% (28057)Memory used [KB]: 10746
fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).

% (28057)Time elapsed: 0.140 s
% (28057)------------------------------
% (28057)------------------------------
fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f250,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0) ),
    inference(forward_demodulation,[],[f226,f93])).

fof(f93,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f91,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(X0))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f49,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f91,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f90,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | r1_tarski(X0,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != X2
      | r1_tarski(X3,X4)
      | ~ r1_tarski(X3,X2) ) ),
    inference(resolution,[],[f86,f44])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 != X1
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f81,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | k1_xboole_0 != X1 ) ),
    inference(resolution,[],[f48,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k1_xboole_0 != X0 ) ),
    inference(subsumption_resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ r1_tarski(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f69,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f69,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f40,f59])).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f46,f50])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f226,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f29,f224])).

fof(f224,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f194,f94])).

fof(f94,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f91,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f194,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f28,f178])).

fof(f178,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f177,f28])).

fof(f177,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f164,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f164,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f144,f143])).

fof(f143,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f140,f112])).

fof(f112,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f33,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f140,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f36,f30])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f144,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f29,f142])).

fof(f142,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f139,f111])).

fof(f111,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f33,f27])).

fof(f139,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f36,f27])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:17:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (28051)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (28050)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (28059)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (28041)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (28058)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (28043)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (28042)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (28043)Refutation not found, incomplete strategy% (28043)------------------------------
% 0.21/0.55  % (28043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (28049)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (28043)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (28043)Memory used [KB]: 10746
% 0.21/0.56  % (28043)Time elapsed: 0.121 s
% 0.21/0.56  % (28043)------------------------------
% 0.21/0.56  % (28043)------------------------------
% 1.54/0.57  % (28057)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.57  % (28041)Refutation found. Thanks to Tanya!
% 1.54/0.57  % SZS status Theorem for theBenchmark
% 1.54/0.58  % (28057)Refutation not found, incomplete strategy% (28057)------------------------------
% 1.54/0.58  % (28057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (28048)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f251,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(subsumption_resolution,[],[f250,f125])).
% 1.54/0.58  fof(f125,plain,(
% 1.54/0.58    r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 1.54/0.58    inference(resolution,[],[f121,f45])).
% 1.54/0.58  fof(f45,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f9,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.54/0.58  % (28057)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  fof(f121,plain,(
% 1.54/0.58    m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.54/0.58    inference(resolution,[],[f34,f27])).
% 1.54/0.58  
% 1.54/0.58  % (28057)Memory used [KB]: 10746
% 1.54/0.58  fof(f27,plain,(
% 1.54/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.54/0.58    inference(cnf_transformation,[],[f16])).
% 1.54/0.58  % (28057)Time elapsed: 0.140 s
% 1.54/0.58  % (28057)------------------------------
% 1.54/0.58  % (28057)------------------------------
% 1.54/0.58  fof(f16,plain,(
% 1.54/0.58    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(flattening,[],[f15])).
% 1.54/0.58  fof(f15,plain,(
% 1.54/0.58    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f13])).
% 1.54/0.58  fof(f13,negated_conjecture,(
% 1.54/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.54/0.58    inference(negated_conjecture,[],[f12])).
% 1.54/0.58  fof(f12,conjecture,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.54/0.58  fof(f34,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f22])).
% 1.54/0.58  fof(f22,plain,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.54/0.58  fof(f250,plain,(
% 1.54/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0)),
% 1.54/0.58    inference(forward_demodulation,[],[f226,f93])).
% 1.54/0.58  fof(f93,plain,(
% 1.54/0.58    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(resolution,[],[f91,f82])).
% 1.54/0.58  fof(f82,plain,(
% 1.54/0.58    ( ! [X0] : (~r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(resolution,[],[f49,f44])).
% 1.54/0.58  fof(f44,plain,(
% 1.54/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f9])).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.54/0.58    inference(equality_resolution,[],[f35])).
% 1.54/0.58  fof(f35,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f23])).
% 1.54/0.58  fof(f23,plain,(
% 1.54/0.58    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.54/0.58  fof(f91,plain,(
% 1.54/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.54/0.58    inference(resolution,[],[f90,f50])).
% 1.54/0.58  fof(f50,plain,(
% 1.54/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.54/0.58    inference(equality_resolution,[],[f38])).
% 1.54/0.58  fof(f38,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.54/0.58    inference(cnf_transformation,[],[f2])).
% 1.54/0.58  fof(f2,axiom,(
% 1.54/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.54/0.58  fof(f90,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_tarski(X0,k1_xboole_0) | r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(equality_resolution,[],[f89])).
% 1.54/0.58  fof(f89,plain,(
% 1.54/0.58    ( ! [X4,X2,X3] : (k1_xboole_0 != X2 | r1_tarski(X3,X4) | ~r1_tarski(X3,X2)) )),
% 1.54/0.58    inference(resolution,[],[f86,f44])).
% 1.54/0.58  fof(f86,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 != X1 | r1_tarski(X0,X2)) )),
% 1.54/0.58    inference(resolution,[],[f81,f42])).
% 1.54/0.58  fof(f42,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f25])).
% 1.54/0.58  fof(f25,plain,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f1])).
% 1.54/0.58  fof(f1,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.54/0.58  fof(f81,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | k1_xboole_0 != X1) )),
% 1.54/0.58    inference(resolution,[],[f48,f71])).
% 1.54/0.58  fof(f71,plain,(
% 1.54/0.58    ( ! [X0] : (v1_xboole_0(X0) | k1_xboole_0 != X0) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f70,f50])).
% 1.54/0.58  fof(f70,plain,(
% 1.54/0.58    ( ! [X0] : (k1_xboole_0 != X0 | ~r1_tarski(X0,X0) | v1_xboole_0(X0)) )),
% 1.54/0.58    inference(resolution,[],[f69,f31])).
% 1.54/0.58  fof(f31,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f18])).
% 1.54/0.58  fof(f18,plain,(
% 1.54/0.58    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.54/0.58    inference(flattening,[],[f17])).
% 1.54/0.58  fof(f17,plain,(
% 1.54/0.58    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f4])).
% 1.54/0.58  fof(f4,axiom,(
% 1.54/0.58    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.54/0.58  fof(f69,plain,(
% 1.54/0.58    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.54/0.58    inference(superposition,[],[f40,f59])).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.54/0.58    inference(resolution,[],[f46,f50])).
% 1.54/0.58  fof(f46,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f3])).
% 1.54/0.58  fof(f3,axiom,(
% 1.54/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.54/0.58  fof(f40,plain,(
% 1.54/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f24])).
% 1.54/0.58  fof(f24,plain,(
% 1.54/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 1.54/0.58    inference(ennf_transformation,[],[f14])).
% 1.54/0.58  fof(f14,plain,(
% 1.54/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 1.54/0.58    inference(unused_predicate_definition_removal,[],[f5])).
% 1.54/0.58  fof(f5,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.54/0.58  fof(f48,plain,(
% 1.54/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f26])).
% 1.54/0.58  fof(f26,plain,(
% 1.54/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f10])).
% 1.54/0.58  fof(f10,axiom,(
% 1.54/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.54/0.58  fof(f226,plain,(
% 1.54/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))),
% 1.54/0.58    inference(backward_demodulation,[],[f29,f224])).
% 1.54/0.58  fof(f224,plain,(
% 1.54/0.58    k1_xboole_0 = sK1),
% 1.54/0.58    inference(subsumption_resolution,[],[f194,f94])).
% 1.54/0.58  fof(f94,plain,(
% 1.54/0.58    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.54/0.58    inference(resolution,[],[f91,f39])).
% 1.54/0.58  fof(f39,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.54/0.58    inference(cnf_transformation,[],[f2])).
% 1.54/0.58  fof(f194,plain,(
% 1.54/0.58    r1_tarski(sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.54/0.58    inference(superposition,[],[f28,f178])).
% 1.54/0.58  fof(f178,plain,(
% 1.54/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.54/0.58    inference(subsumption_resolution,[],[f177,f28])).
% 1.54/0.58  fof(f177,plain,(
% 1.54/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 1.54/0.58    inference(duplicate_literal_removal,[],[f175])).
% 1.54/0.58  fof(f175,plain,(
% 1.54/0.58    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2)),
% 1.54/0.58    inference(resolution,[],[f164,f32])).
% 1.54/0.58  fof(f32,plain,(
% 1.54/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f20])).
% 1.54/0.58  fof(f20,plain,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.54/0.58    inference(flattening,[],[f19])).
% 1.54/0.58  fof(f19,plain,(
% 1.54/0.58    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.54/0.58    inference(ennf_transformation,[],[f11])).
% 1.54/0.58  fof(f11,axiom,(
% 1.54/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.54/0.58  fof(f164,plain,(
% 1.54/0.58    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.54/0.58    inference(superposition,[],[f144,f143])).
% 1.54/0.58  fof(f143,plain,(
% 1.54/0.58    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | k1_xboole_0 = sK1),
% 1.54/0.58    inference(forward_demodulation,[],[f140,f112])).
% 1.54/0.58  fof(f112,plain,(
% 1.54/0.58    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.54/0.58    inference(resolution,[],[f33,f30])).
% 1.54/0.58  fof(f30,plain,(
% 1.54/0.58    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.54/0.58    inference(cnf_transformation,[],[f16])).
% 1.54/0.58  fof(f33,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f21])).
% 1.54/0.58  fof(f21,plain,(
% 1.54/0.58    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.54/0.58    inference(ennf_transformation,[],[f8])).
% 1.54/0.58  fof(f8,axiom,(
% 1.54/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.54/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.54/0.58  fof(f140,plain,(
% 1.54/0.58    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 1.54/0.58    inference(resolution,[],[f36,f30])).
% 1.54/0.58  fof(f36,plain,(
% 1.54/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.54/0.58    inference(cnf_transformation,[],[f23])).
% 1.54/0.58  fof(f144,plain,(
% 1.54/0.58    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | k1_xboole_0 = sK2),
% 1.54/0.58    inference(superposition,[],[f29,f142])).
% 1.54/0.58  fof(f142,plain,(
% 1.54/0.58    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | k1_xboole_0 = sK2),
% 1.54/0.58    inference(forward_demodulation,[],[f139,f111])).
% 1.54/0.58  fof(f111,plain,(
% 1.54/0.58    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.54/0.58    inference(resolution,[],[f33,f27])).
% 1.54/0.58  fof(f139,plain,(
% 1.54/0.58    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.54/0.58    inference(resolution,[],[f36,f27])).
% 1.54/0.58  fof(f28,plain,(
% 1.54/0.58    r1_tarski(sK1,sK2)),
% 1.54/0.58    inference(cnf_transformation,[],[f16])).
% 1.54/0.58  fof(f29,plain,(
% 1.54/0.58    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.54/0.58    inference(cnf_transformation,[],[f16])).
% 1.54/0.58  % SZS output end Proof for theBenchmark
% 1.54/0.58  % (28041)------------------------------
% 1.54/0.58  % (28041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (28041)Termination reason: Refutation
% 1.54/0.58  
% 1.54/0.58  % (28041)Memory used [KB]: 6396
% 1.54/0.58  % (28041)Time elapsed: 0.129 s
% 1.54/0.58  % (28041)------------------------------
% 1.54/0.58  % (28041)------------------------------
% 1.54/0.59  % (28033)Success in time 0.22 s
%------------------------------------------------------------------------------
