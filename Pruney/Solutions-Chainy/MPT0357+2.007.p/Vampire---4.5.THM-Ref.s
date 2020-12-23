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
% DateTime   : Thu Dec  3 12:44:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   85 (1094 expanded)
%              Number of leaves         :   16 ( 365 expanded)
%              Depth                    :   19
%              Number of atoms          :  142 (2326 expanded)
%              Number of equality atoms :   47 ( 676 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f707,plain,(
    $false ),
    inference(subsumption_resolution,[],[f706,f387])).

fof(f387,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(backward_demodulation,[],[f29,f375])).

fof(f375,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f205,f312])).

fof(f312,plain,(
    sK2 = k6_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f302,f192])).

fof(f192,plain,(
    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    inference(resolution,[],[f51,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
    & r1_tarski(k3_subset_1(sK0,sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
            & r1_tarski(k3_subset_1(X0,X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
          & r1_tarski(k3_subset_1(sK0,sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK0,X2),sK1)
        & r1_tarski(k3_subset_1(sK0,sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(k3_subset_1(sK0,sK2),sK1)
      & r1_tarski(k3_subset_1(sK0,sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X2),X1)
          & r1_tarski(k3_subset_1(X0,X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(k3_subset_1(X0,X1),X2)
             => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(k3_subset_1(X0,X1),X2)
           => r1_tarski(k3_subset_1(X0,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f302,plain,(
    sK2 = k6_subset_1(sK0,k6_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f271,f48])).

fof(f48,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f44,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38,f38])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f271,plain,(
    sK2 = k6_subset_1(sK2,k6_subset_1(sK2,sK0)) ),
    inference(resolution,[],[f265,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f265,plain,(
    r1_tarski(sK2,sK0) ),
    inference(resolution,[],[f254,f27])).

fof(f254,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | r1_tarski(X2,X3) ) ),
    inference(forward_demodulation,[],[f253,f46])).

fof(f46,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f32,f45])).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f32,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f253,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k3_subset_1(X3,k1_xboole_0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f247,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f247,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,k3_subset_1(X3,k1_xboole_0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f43,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f205,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK2))) ),
    inference(superposition,[],[f49,f192])).

fof(f49,plain,(
    ! [X0,X1] : k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f38,f44])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f29,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f706,plain,(
    r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(forward_demodulation,[],[f705,f456])).

fof(f456,plain,(
    sK1 = k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f455,f353])).

fof(f353,plain,(
    sK1 = k6_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f282,f332])).

fof(f332,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    inference(backward_demodulation,[],[f199,f282])).

fof(f199,plain,(
    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK1))) ),
    inference(superposition,[],[f49,f191])).

fof(f191,plain,(
    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f51,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f282,plain,(
    sK1 = k6_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f272,f191])).

fof(f272,plain,(
    sK1 = k6_subset_1(sK0,k6_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f270,f48])).

fof(f270,plain,(
    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,sK0)) ),
    inference(resolution,[],[f264,f50])).

fof(f264,plain,(
    r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f254,f26])).

fof(f455,plain,(
    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k6_subset_1(sK0,k5_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f204,f332])).

fof(f204,plain,(
    k6_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f201,f51])).

fof(f201,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f36,f191])).

fof(f36,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f705,plain,(
    r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f697,f340])).

fof(f340,plain,(
    r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(backward_demodulation,[],[f28,f332])).

fof(f28,plain,(
    r1_tarski(k3_subset_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f697,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f463,f350])).

fof(f350,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f201,f332])).

fof(f463,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,X0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f462,f384])).

fof(f384,plain,(
    m1_subset_1(k5_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(backward_demodulation,[],[f207,f375])).

fof(f207,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f36,f192])).

fof(f462,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,X0))
      | ~ m1_subset_1(k5_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f43,f461])).

fof(f461,plain,(
    sK2 = k3_subset_1(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f460,f383])).

fof(f383,plain,(
    sK2 = k6_subset_1(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f312,f375])).

fof(f460,plain,(
    k6_subset_1(sK0,k5_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k5_xboole_0(sK0,sK2)) ),
    inference(forward_demodulation,[],[f210,f375])).

fof(f210,plain,(
    k6_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f207,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (27282)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (27281)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (27283)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (27290)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (27279)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (27289)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (27286)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (27287)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.49  % (27280)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (27290)Refutation not found, incomplete strategy% (27290)------------------------------
% 0.22/0.49  % (27290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (27290)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (27290)Memory used [KB]: 10874
% 0.22/0.49  % (27290)Time elapsed: 0.076 s
% 0.22/0.49  % (27290)------------------------------
% 0.22/0.49  % (27290)------------------------------
% 0.22/0.49  % (27295)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (27291)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (27296)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.50  % (27284)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (27285)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (27293)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (27294)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (27292)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (27288)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.52  % (27291)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f707,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f706,f387])).
% 0.22/0.52  fof(f387,plain,(
% 0.22/0.52    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f29,f375])).
% 0.22/0.52  fof(f375,plain,(
% 0.22/0.52    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f205,f312])).
% 0.22/0.52  fof(f312,plain,(
% 0.22/0.52    sK2 = k6_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f302,f192])).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 0.22/0.52    inference(resolution,[],[f51,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f24,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X2] : (~r1_tarski(k3_subset_1(sK0,X2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(k3_subset_1(sK0,sK2),sK1) & r1_tarski(k3_subset_1(sK0,sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),X1) & r1_tarski(k3_subset_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f15])).
% 0.22/0.52  fof(f15,conjecture,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X2) => r1_tarski(k3_subset_1(X0,X2),X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_subset_1)).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f42,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.52  fof(f302,plain,(
% 0.22/0.52    sK2 = k6_subset_1(sK0,k6_subset_1(sK0,sK2))),
% 0.22/0.52    inference(superposition,[],[f271,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X1,k6_subset_1(X1,X0))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f37,f44,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f39,f38,f38])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.52  fof(f271,plain,(
% 0.22/0.52    sK2 = k6_subset_1(sK2,k6_subset_1(sK2,sK0))),
% 0.22/0.52    inference(resolution,[],[f265,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_subset_1(X0,k6_subset_1(X0,X1)) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f41,f44])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f265,plain,(
% 0.22/0.52    r1_tarski(sK2,sK0)),
% 0.22/0.52    inference(resolution,[],[f254,f27])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | r1_tarski(X2,X3)) )),
% 0.22/0.52    inference(forward_demodulation,[],[f253,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(definition_unfolding,[],[f32,f45])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f34,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,axiom,(
% 0.22/0.52    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.52  fof(f253,plain,(
% 0.22/0.52    ( ! [X2,X3] : (r1_tarski(X2,k3_subset_1(X3,k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f247,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f247,plain,(
% 0.22/0.52    ( ! [X2,X3] : (r1_tarski(X2,k3_subset_1(X3,k1_xboole_0)) | ~m1_subset_1(X2,k1_zfmisc_1(X3)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X3))) )),
% 0.22/0.52    inference(resolution,[],[f43,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,axiom,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK2)))),
% 0.22/0.52    inference(superposition,[],[f49,f192])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k5_xboole_0(X0,k6_subset_1(X0,k6_subset_1(X0,X1)))) )),
% 0.22/0.52    inference(definition_unfolding,[],[f40,f38,f44])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ~r1_tarski(k3_subset_1(sK0,sK2),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f706,plain,(
% 0.22/0.52    r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.22/0.52    inference(forward_demodulation,[],[f705,f456])).
% 0.22/0.52  fof(f456,plain,(
% 0.22/0.52    sK1 = k3_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f455,f353])).
% 0.22/0.52  fof(f353,plain,(
% 0.22/0.52    sK1 = k6_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(backward_demodulation,[],[f282,f332])).
% 0.22/0.52  fof(f332,plain,(
% 0.22/0.52    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(backward_demodulation,[],[f199,f282])).
% 0.22/0.52  fof(f199,plain,(
% 0.22/0.52    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k6_subset_1(sK0,k3_subset_1(sK0,sK1)))),
% 0.22/0.52    inference(superposition,[],[f49,f191])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)),
% 0.22/0.52    inference(resolution,[],[f51,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f282,plain,(
% 0.22/0.52    sK1 = k6_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f272,f191])).
% 0.22/0.52  fof(f272,plain,(
% 0.22/0.52    sK1 = k6_subset_1(sK0,k6_subset_1(sK0,sK1))),
% 0.22/0.52    inference(superposition,[],[f270,f48])).
% 0.22/0.52  fof(f270,plain,(
% 0.22/0.52    sK1 = k6_subset_1(sK1,k6_subset_1(sK1,sK0))),
% 0.22/0.52    inference(resolution,[],[f264,f50])).
% 0.22/0.52  fof(f264,plain,(
% 0.22/0.52    r1_tarski(sK1,sK0)),
% 0.22/0.52    inference(resolution,[],[f254,f26])).
% 0.22/0.52  fof(f455,plain,(
% 0.22/0.52    k3_subset_1(sK0,k5_xboole_0(sK0,sK1)) = k6_subset_1(sK0,k5_xboole_0(sK0,sK1))),
% 0.22/0.52    inference(forward_demodulation,[],[f204,f332])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    k6_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.22/0.52    inference(resolution,[],[f201,f51])).
% 0.22/0.52  fof(f201,plain,(
% 0.22/0.52    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(superposition,[],[f36,f191])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,axiom,(
% 0.22/0.52    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.22/0.52  fof(f705,plain,(
% 0.22/0.52    r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,k5_xboole_0(sK0,sK1)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f697,f340])).
% 0.22/0.52  fof(f340,plain,(
% 0.22/0.52    r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 0.22/0.52    inference(backward_demodulation,[],[f28,f332])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    r1_tarski(k3_subset_1(sK0,sK1),sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f697,plain,(
% 0.22/0.52    r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,k5_xboole_0(sK0,sK1))) | ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 0.22/0.52    inference(resolution,[],[f463,f350])).
% 0.22/0.52  fof(f350,plain,(
% 0.22/0.52    m1_subset_1(k5_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(backward_demodulation,[],[f201,f332])).
% 0.22/0.52  fof(f463,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,X0)) | ~r1_tarski(X0,sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f462,f384])).
% 0.22/0.52  fof(f384,plain,(
% 0.22/0.52    m1_subset_1(k5_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(backward_demodulation,[],[f207,f375])).
% 0.22/0.52  fof(f207,plain,(
% 0.22/0.52    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.52    inference(superposition,[],[f36,f192])).
% 0.22/0.52  fof(f462,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_tarski(k5_xboole_0(sK0,sK2),k3_subset_1(sK0,X0)) | ~m1_subset_1(k5_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.22/0.52    inference(superposition,[],[f43,f461])).
% 0.22/0.52  fof(f461,plain,(
% 0.22/0.52    sK2 = k3_subset_1(sK0,k5_xboole_0(sK0,sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f460,f383])).
% 0.22/0.52  fof(f383,plain,(
% 0.22/0.52    sK2 = k6_subset_1(sK0,k5_xboole_0(sK0,sK2))),
% 0.22/0.52    inference(backward_demodulation,[],[f312,f375])).
% 0.22/0.52  fof(f460,plain,(
% 0.22/0.52    k6_subset_1(sK0,k5_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k5_xboole_0(sK0,sK2))),
% 0.22/0.52    inference(forward_demodulation,[],[f210,f375])).
% 0.22/0.52  fof(f210,plain,(
% 0.22/0.52    k6_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 0.22/0.52    inference(resolution,[],[f207,f51])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (27291)------------------------------
% 0.22/0.52  % (27291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (27291)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (27291)Memory used [KB]: 1791
% 0.22/0.52  % (27291)Time elapsed: 0.104 s
% 0.22/0.52  % (27291)------------------------------
% 0.22/0.52  % (27291)------------------------------
% 0.22/0.52  % (27278)Success in time 0.159 s
%------------------------------------------------------------------------------
