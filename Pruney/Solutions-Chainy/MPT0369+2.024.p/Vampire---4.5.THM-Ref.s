%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 178 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  139 ( 399 expanded)
%              Number of equality atoms :   36 ( 105 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f134,plain,(
    $false ),
    inference(subsumption_resolution,[],[f133,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,k3_subset_1(X0,X1))
              & ~ r2_hidden(X2,X1)
              & m1_subset_1(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( k1_xboole_0 != X0
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(X0))
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ( ~ r2_hidden(X2,X1)
                 => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f133,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f130,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f130,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f129,f84])).

fof(f84,plain,(
    ~ r2_hidden(sK2,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f29,f82])).

fof(f82,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f45,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f29,plain,(
    ~ r2_hidden(sK2,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f129,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK0,sK1))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f128,f93])).

fof(f93,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(backward_demodulation,[],[f73,f92])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f86,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f86,plain,(
    ! [X1] : k4_xboole_0(X1,X1) = k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1)) ),
    inference(superposition,[],[f54,f70])).

fof(f70,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f67,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f67,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f49,f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f73,plain,(
    ! [X1] : k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1 ),
    inference(resolution,[],[f44,f67])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f128,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f121,f28])).

fof(f28,plain,(
    ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f121,plain,
    ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))
    | r2_hidden(sK2,sK1)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f114,f99])).

fof(f99,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f98,f93])).

fof(f98,plain,(
    k4_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f88,f92])).

fof(f88,plain,(
    k4_xboole_0(sK1,sK0) = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f54,f81])).

fof(f81,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f78,f43])).

fof(f78,plain,(
    r1_tarski(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f114,plain,(
    ! [X0] :
      ( r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X0,sK0)))
      | r2_hidden(sK2,X0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f57,f61])).

fof(f61,plain,
    ( r2_hidden(sK2,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2)
      | r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) ),
    inference(definition_unfolding,[],[f53,f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.50  % (31753)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.50  % (31753)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (31777)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.51  % (31760)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    k1_xboole_0 != sK0),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k3_subset_1(X0,X1)) & ~r2_hidden(X2,X1)) & m1_subset_1(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) & k1_xboole_0 != X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    k1_xboole_0 = sK0),
% 0.22/0.51    inference(resolution,[],[f130,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f129,f84])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ~r2_hidden(sK2,k4_xboole_0(sK0,sK1))),
% 0.22/0.51    inference(backward_demodulation,[],[f29,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.22/0.51    inference(resolution,[],[f45,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ~r2_hidden(sK2,k3_subset_1(sK0,sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f129,plain,(
% 0.22/0.51    r2_hidden(sK2,k4_xboole_0(sK0,sK1)) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f128,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.22/0.51    inference(backward_demodulation,[],[f73,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f86,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k2_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f34,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X1] : (k4_xboole_0(X1,X1) = k2_xboole_0(k4_xboole_0(X1,X1),k4_xboole_0(X1,X1))) )),
% 0.22/0.51    inference(superposition,[],[f54,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 0.22/0.51    inference(resolution,[],[f67,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.51    inference(resolution,[],[f49,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),k4_xboole_0(k3_xboole_0(X0,X1),X0))) )),
% 0.22/0.51    inference(definition_unfolding,[],[f37,f38])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X1)) = X1) )),
% 0.22/0.51    inference(resolution,[],[f44,f67])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f121,f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ~r2_hidden(sK2,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) | r2_hidden(sK2,sK1) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(superposition,[],[f114,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK1,sK0)),
% 0.22/0.51    inference(forward_demodulation,[],[f98,f93])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    k4_xboole_0(sK1,sK0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(forward_demodulation,[],[f88,f92])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    k4_xboole_0(sK1,sK0) = k2_xboole_0(k4_xboole_0(sK1,sK1),k4_xboole_0(sK1,sK1))),
% 0.22/0.51    inference(superposition,[],[f54,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    sK1 = k3_xboole_0(sK1,sK0)),
% 0.22/0.51    inference(resolution,[],[f78,f43])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    r1_tarski(sK1,sK0)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    r1_tarski(sK1,sK0) | r1_tarski(sK1,sK0)),
% 0.22/0.51    inference(resolution,[],[f76,f49])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK3(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f74,f48])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.22/0.51    inference(resolution,[],[f46,f30])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK2,k2_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(X0,sK0))) | r2_hidden(sK2,X0) | v1_xboole_0(sK0)) )),
% 0.22/0.51    inference(resolution,[],[f57,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    r2_hidden(sK2,sK0) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f42,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    m1_subset_1(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 1.22/0.51  fof(f20,plain,(
% 1.22/0.51    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.22/0.51    inference(ennf_transformation,[],[f12])).
% 1.22/0.51  fof(f12,axiom,(
% 1.22/0.51    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.22/0.51  fof(f57,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,X2) | r2_hidden(X0,k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X2,X1)))) )),
% 1.22/0.51    inference(definition_unfolding,[],[f53,f38])).
% 1.22/0.51  fof(f53,plain,(
% 1.22/0.51    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 1.22/0.51    inference(cnf_transformation,[],[f26])).
% 1.22/0.51  fof(f26,plain,(
% 1.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.22/0.51    inference(ennf_transformation,[],[f4])).
% 1.22/0.51  fof(f4,axiom,(
% 1.22/0.51    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.22/0.51  % SZS output end Proof for theBenchmark
% 1.22/0.51  % (31753)------------------------------
% 1.22/0.51  % (31753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (31753)Termination reason: Refutation
% 1.22/0.51  
% 1.22/0.51  % (31753)Memory used [KB]: 6268
% 1.22/0.51  % (31753)Time elapsed: 0.087 s
% 1.22/0.51  % (31753)------------------------------
% 1.22/0.51  % (31753)------------------------------
% 1.22/0.52  % (31745)Success in time 0.158 s
%------------------------------------------------------------------------------
