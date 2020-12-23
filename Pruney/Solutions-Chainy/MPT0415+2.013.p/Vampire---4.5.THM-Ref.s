%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 208 expanded)
%              Number of leaves         :   16 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  158 ( 368 expanded)
%              Number of equality atoms :   59 ( 195 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f160,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f29])).

fof(f29,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k7_setfam_1(X0,X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f159,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f157,f96])).

fof(f96,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f93,f29])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f86,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 = X2
      | m1_subset_1(sK2(X2),X3) ) ),
    inference(resolution,[],[f84,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f84,plain,(
    ! [X1] :
      ( r2_hidden(sK2(X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f81,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,X1)
      | k1_xboole_0 = X1
      | r2_hidden(X2,X1) ) ),
    inference(forward_demodulation,[],[f80,f76])).

% (24022)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f76,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f75,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f73,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f32,f52])).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f73,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) ),
    inference(resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

% (23996)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f53,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f80,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = X1
      | ~ m1_subset_1(X2,X1)
      | r2_hidden(X2,k3_subset_1(X1,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f63,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f63,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k1_tarski(X0),k1_tarski(X0))) ),
    inference(superposition,[],[f62,f55])).

fof(f55,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f52])).

fof(f37,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f62,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2))))) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2))))) ) ),
    inference(definition_unfolding,[],[f50,f53])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f78,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = X1
      | ~ m1_subset_1(X2,X1)
      | r2_hidden(X2,k1_xboole_0)
      | r2_hidden(X2,k3_subset_1(X1,k1_xboole_0)) ) ),
    inference(resolution,[],[f35,f31])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,X1)
      | r2_hidden(X2,k3_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

fof(f157,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0))
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f155,f84])).

fof(f155,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f154,f64])).

fof(f154,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f153,f31])).

fof(f153,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f150,f28])).

fof(f150,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f60,f68])).

fof(f68,plain,(
    sK1 = k7_setfam_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f65,f30])).

fof(f30,plain,(
    k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f42,f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (23997)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (23995)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24003)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (24003)Refutation not found, incomplete strategy% (24003)------------------------------
% 0.20/0.51  % (24003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24003)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24003)Memory used [KB]: 10746
% 0.20/0.51  % (24003)Time elapsed: 0.093 s
% 0.20/0.51  % (24003)------------------------------
% 0.20/0.51  % (24003)------------------------------
% 0.20/0.52  % (24011)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (24005)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (24009)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (23999)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (24000)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (24020)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (23999)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (24015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (23993)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (24007)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (23994)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (24012)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (24002)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (24015)Refutation not found, incomplete strategy% (24015)------------------------------
% 0.20/0.54  % (24015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f159,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    k1_xboole_0 != sK1),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ? [X0,X1] : (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0,X1] : ((k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    k1_xboole_0 = sK1),
% 0.20/0.54    inference(subsumption_resolution,[],[f157,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(subsumption_resolution,[],[f93,f29])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    k1_xboole_0 = sK1 | m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.54    inference(resolution,[],[f86,f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(X3)) | k1_xboole_0 = X2 | m1_subset_1(sK2(X2),X3)) )),
% 0.20/0.54    inference(resolution,[],[f84,f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    ( ! [X1] : (r2_hidden(sK2(X1),X1) | k1_xboole_0 = X1) )),
% 0.20/0.54    inference(resolution,[],[f81,f36])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~m1_subset_1(X2,X1) | k1_xboole_0 = X1 | r2_hidden(X2,X1)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f80,f76])).
% 0.20/0.55  % (24022)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(forward_demodulation,[],[f75,f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f73,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f32,f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f38,f39])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,axiom,(
% 0.20/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.55  fof(f32,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.55  fof(f73,plain,(
% 0.20/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)))) )),
% 0.20/0.55    inference(resolution,[],[f56,f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f10])).
% 0.20/0.55  % (23996)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f41,f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.55    inference(definition_unfolding,[],[f40,f52])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X1] : (k1_xboole_0 = X1 | ~m1_subset_1(X2,X1) | r2_hidden(X2,k3_subset_1(X1,k1_xboole_0))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f78,f64])).
% 0.20/0.55  fof(f64,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f63,f33])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.55  fof(f63,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_tarski(X0),k1_tarski(X0)))) )),
% 0.20/0.55    inference(superposition,[],[f62,f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,X0)) = X0) )),
% 0.20/0.55    inference(definition_unfolding,[],[f37,f52])).
% 1.46/0.55  fof(f37,plain,(
% 1.46/0.55    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.46/0.55    inference(cnf_transformation,[],[f18])).
% 1.46/0.55  fof(f18,plain,(
% 1.46/0.55    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.46/0.55    inference(rectify,[],[f1])).
% 1.46/0.55  fof(f1,axiom,(
% 1.46/0.55    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.46/0.55  fof(f62,plain,(
% 1.46/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2)))))) )),
% 1.46/0.55    inference(equality_resolution,[],[f58])).
% 1.46/0.55  fof(f58,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k1_enumset1(X1,X1,k1_tarski(X2)))))) )),
% 1.46/0.55    inference(definition_unfolding,[],[f50,f53])).
% 1.46/0.55  fof(f50,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f7])).
% 1.46/0.55  fof(f7,axiom,(
% 1.46/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.46/0.55  fof(f78,plain,(
% 1.46/0.55    ( ! [X2,X1] : (k1_xboole_0 = X1 | ~m1_subset_1(X2,X1) | r2_hidden(X2,k1_xboole_0) | r2_hidden(X2,k3_subset_1(X1,k1_xboole_0))) )),
% 1.46/0.55    inference(resolution,[],[f35,f31])).
% 1.46/0.55  fof(f35,plain,(
% 1.46/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X2,X0) | r2_hidden(X2,X1) | r2_hidden(X2,k3_subset_1(X0,X1))) )),
% 1.46/0.55    inference(cnf_transformation,[],[f22])).
% 1.46/0.55  fof(f22,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.46/0.55    inference(flattening,[],[f21])).
% 1.46/0.55  fof(f21,plain,(
% 1.46/0.55    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 1.46/0.55    inference(ennf_transformation,[],[f11])).
% 1.46/0.55  fof(f11,axiom,(
% 1.46/0.55    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).
% 1.46/0.55  fof(f157,plain,(
% 1.46/0.55    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(sK0)) | k1_xboole_0 = sK1),
% 1.46/0.55    inference(resolution,[],[f155,f84])).
% 1.46/0.55  fof(f155,plain,(
% 1.46/0.55    ( ! [X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(sK0))) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f154,f64])).
% 1.46/0.55  fof(f154,plain,(
% 1.46/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f153,f31])).
% 1.46/0.55  fof(f153,plain,(
% 1.46/0.55    ( ! [X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1)) )),
% 1.46/0.55    inference(subsumption_resolution,[],[f150,f28])).
% 1.46/0.55  fof(f150,plain,(
% 1.46/0.55    ( ! [X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k3_subset_1(sK0,X1),k1_xboole_0) | ~r2_hidden(X1,sK1)) )),
% 1.46/0.55    inference(superposition,[],[f60,f68])).
% 1.46/0.55  fof(f68,plain,(
% 1.46/0.55    sK1 = k7_setfam_1(sK0,k1_xboole_0)),
% 1.46/0.55    inference(forward_demodulation,[],[f65,f30])).
% 1.46/0.55  fof(f30,plain,(
% 1.46/0.55    k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.46/0.55    inference(cnf_transformation,[],[f20])).
% 1.46/0.55  fof(f65,plain,(
% 1.46/0.55    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 1.46/0.55    inference(resolution,[],[f42,f28])).
% 1.46/0.55  fof(f42,plain,(
% 1.46/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 1.46/0.55    inference(cnf_transformation,[],[f24])).
% 1.46/0.55  fof(f24,plain,(
% 1.46/0.55    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.46/0.55    inference(ennf_transformation,[],[f13])).
% 1.46/0.55  fof(f13,axiom,(
% 1.46/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.46/0.55  fof(f60,plain,(
% 1.46/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,k7_setfam_1(X0,X1))) )),
% 1.46/0.55    inference(equality_resolution,[],[f46])).
% 1.46/0.55  fof(f46,plain,(
% 1.46/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | r2_hidden(k3_subset_1(X0,X3),X1) | ~r2_hidden(X3,X2) | k7_setfam_1(X0,X1) != X2) )),
% 1.46/0.55    inference(cnf_transformation,[],[f25])).
% 1.46/0.55  fof(f25,plain,(
% 1.46/0.55    ! [X0,X1] : (! [X2] : ((k7_setfam_1(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.46/0.55    inference(ennf_transformation,[],[f12])).
% 1.46/0.55  fof(f12,axiom,(
% 1.46/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k7_setfam_1(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X2) <=> r2_hidden(k3_subset_1(X0,X3),X1))))))),
% 1.46/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).
% 1.46/0.55  % SZS output end Proof for theBenchmark
% 1.46/0.55  % (23999)------------------------------
% 1.46/0.55  % (23999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (23999)Termination reason: Refutation
% 1.46/0.55  
% 1.46/0.55  % (23999)Memory used [KB]: 6396
% 1.46/0.55  % (23999)Time elapsed: 0.116 s
% 1.46/0.55  % (23999)------------------------------
% 1.46/0.55  % (23999)------------------------------
% 1.46/0.55  % (24015)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  % (23992)Success in time 0.193 s
%------------------------------------------------------------------------------
