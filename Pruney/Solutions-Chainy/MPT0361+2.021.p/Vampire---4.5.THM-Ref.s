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
% DateTime   : Thu Dec  3 12:45:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   40 (  75 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   73 ( 162 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f319,f61])).

fof(f61,plain,(
    ! [X4,X5,X3] : r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4)) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3))
      | r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f319,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f85,f96])).

fof(f96,plain,(
    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f87,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f87,plain,(
    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f86,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f86,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f84,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f84,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f25,f43])).

fof(f43,plain,(
    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f38,f19])).

fof(f38,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2) ) ),
    inference(resolution,[],[f26,f17])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f85,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f83,f32])).

fof(f32,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f22,f19])).

fof(f83,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(superposition,[],[f18,f43])).

fof(f18,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:38:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.43  % (24295)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.23/0.44  % (24294)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.23/0.45  % (24292)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.23/0.45  % (24295)Refutation found. Thanks to Tanya!
% 0.23/0.45  % SZS status Theorem for theBenchmark
% 0.23/0.45  % SZS output start Proof for theBenchmark
% 0.23/0.45  fof(f320,plain,(
% 0.23/0.45    $false),
% 0.23/0.45    inference(subsumption_resolution,[],[f319,f61])).
% 0.23/0.45  fof(f61,plain,(
% 0.23/0.45    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X3,k2_xboole_0(X4,X5)),k4_xboole_0(X3,X4))) )),
% 0.23/0.45    inference(resolution,[],[f34,f27])).
% 0.23/0.45  fof(f27,plain,(
% 0.23/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.23/0.45    inference(superposition,[],[f20,f21])).
% 0.23/0.45  fof(f21,plain,(
% 0.23/0.45    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f1])).
% 0.23/0.45  fof(f1,axiom,(
% 0.23/0.45    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.23/0.45  fof(f20,plain,(
% 0.23/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f4])).
% 0.23/0.45  fof(f4,axiom,(
% 0.23/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.23/0.45  fof(f34,plain,(
% 0.23/0.45    ( ! [X2,X0,X3,X1] : (~r1_tarski(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) | r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3)) )),
% 0.23/0.45    inference(superposition,[],[f24,f23])).
% 0.23/0.45  fof(f23,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f2])).
% 0.23/0.45  fof(f2,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.23/0.45  fof(f24,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f12])).
% 0.23/0.45  fof(f12,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.23/0.45    inference(ennf_transformation,[],[f3])).
% 0.23/0.45  fof(f3,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.23/0.45  fof(f319,plain,(
% 0.23/0.45    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.23/0.45    inference(superposition,[],[f85,f96])).
% 0.23/0.45  fof(f96,plain,(
% 0.23/0.45    k3_subset_1(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.23/0.45    inference(resolution,[],[f87,f22])).
% 0.23/0.45  fof(f22,plain,(
% 0.23/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f11])).
% 0.23/0.45  fof(f11,plain,(
% 0.23/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.45    inference(ennf_transformation,[],[f5])).
% 0.23/0.45  fof(f5,axiom,(
% 0.23/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.23/0.45  fof(f87,plain,(
% 0.23/0.45    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.23/0.45    inference(subsumption_resolution,[],[f86,f19])).
% 0.23/0.45  fof(f19,plain,(
% 0.23/0.45    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.45    inference(cnf_transformation,[],[f10])).
% 0.23/0.45  fof(f10,plain,(
% 0.23/0.45    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.45    inference(ennf_transformation,[],[f9])).
% 0.23/0.45  fof(f9,negated_conjecture,(
% 0.23/0.45    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.23/0.45    inference(negated_conjecture,[],[f8])).
% 0.23/0.45  fof(f8,conjecture,(
% 0.23/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 0.23/0.45  fof(f86,plain,(
% 0.23/0.45    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.45    inference(subsumption_resolution,[],[f84,f17])).
% 0.23/0.45  fof(f17,plain,(
% 0.23/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.23/0.45    inference(cnf_transformation,[],[f10])).
% 0.23/0.45  fof(f84,plain,(
% 0.23/0.45    m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.23/0.45    inference(superposition,[],[f25,f43])).
% 0.23/0.45  fof(f43,plain,(
% 0.23/0.45    k4_subset_1(sK0,sK1,sK2) = k2_xboole_0(sK1,sK2)),
% 0.23/0.45    inference(resolution,[],[f38,f19])).
% 0.23/0.45  fof(f38,plain,(
% 0.23/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_xboole_0(X0,sK2) = k4_subset_1(sK0,X0,sK2)) )),
% 0.23/0.45    inference(resolution,[],[f26,f17])).
% 0.23/0.45  fof(f26,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f16])).
% 0.23/0.45  fof(f16,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.45    inference(flattening,[],[f15])).
% 0.23/0.45  fof(f15,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.23/0.45    inference(ennf_transformation,[],[f7])).
% 0.23/0.45  fof(f7,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.23/0.45  fof(f25,plain,(
% 0.23/0.45    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.23/0.45    inference(cnf_transformation,[],[f14])).
% 0.23/0.45  fof(f14,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.23/0.45    inference(flattening,[],[f13])).
% 0.23/0.45  fof(f13,plain,(
% 0.23/0.45    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.23/0.45    inference(ennf_transformation,[],[f6])).
% 0.23/0.45  fof(f6,axiom,(
% 0.23/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.23/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.23/0.45  fof(f85,plain,(
% 0.23/0.45    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK0,sK1))),
% 0.23/0.45    inference(forward_demodulation,[],[f83,f32])).
% 0.23/0.45  fof(f32,plain,(
% 0.23/0.45    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.23/0.45    inference(resolution,[],[f22,f19])).
% 0.23/0.45  fof(f83,plain,(
% 0.23/0.45    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.23/0.45    inference(superposition,[],[f18,f43])).
% 0.23/0.45  fof(f18,plain,(
% 0.23/0.45    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 0.23/0.45    inference(cnf_transformation,[],[f10])).
% 0.23/0.45  % SZS output end Proof for theBenchmark
% 0.23/0.45  % (24295)------------------------------
% 0.23/0.45  % (24295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.45  % (24295)Termination reason: Refutation
% 0.23/0.45  
% 0.23/0.45  % (24295)Memory used [KB]: 11001
% 0.23/0.45  % (24295)Time elapsed: 0.018 s
% 0.23/0.45  % (24295)------------------------------
% 0.23/0.45  % (24295)------------------------------
% 0.23/0.45  % (24296)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.23/0.45  % (24291)Success in time 0.084 s
%------------------------------------------------------------------------------
