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
% DateTime   : Thu Dec  3 12:44:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   67 ( 151 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f307,plain,(
    $false ),
    inference(subsumption_resolution,[],[f297,f37])).

fof(f37,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    & r1_tarski(sK1,k3_subset_1(sK0,sK2))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK1
      & r1_tarski(sK1,k3_subset_1(sK0,sK2))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

fof(f297,plain,(
    k1_xboole_0 = sK1 ),
    inference(superposition,[],[f167,f124])).

fof(f124,plain,(
    ! [X2] : sK1 = k4_xboole_0(sK1,k4_xboole_0(X2,sK2)) ),
    inference(resolution,[],[f84,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f84,plain,(
    ! [X0] : r1_xboole_0(sK1,k4_xboole_0(X0,sK2)) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f167,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f80,f109])).

fof(f109,plain,(
    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f80,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f57,f36])).

fof(f36,plain,(
    r1_tarski(sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (26024)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.44  % (26024)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % (26032)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f307,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f297,f37])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    k1_xboole_0 != sK1),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f23])).
% 0.20/0.44  fof(f23,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK1 & r1_tarski(sK1,k3_subset_1(sK0,sK2)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.44    introduced(choice_axiom,[])).
% 0.20/0.44  fof(f16,plain,(
% 0.20/0.44    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(flattening,[],[f15])).
% 0.20/0.44  fof(f15,plain,(
% 0.20/0.44    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f14])).
% 0.20/0.44  fof(f14,negated_conjecture,(
% 0.20/0.44    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.20/0.44    inference(negated_conjecture,[],[f13])).
% 0.20/0.44  fof(f13,conjecture,(
% 0.20/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).
% 0.20/0.44  fof(f297,plain,(
% 0.20/0.44    k1_xboole_0 = sK1),
% 0.20/0.44    inference(superposition,[],[f167,f124])).
% 0.20/0.44  fof(f124,plain,(
% 0.20/0.44    ( ! [X2] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X2,sK2))) )),
% 0.20/0.44    inference(resolution,[],[f84,f50])).
% 0.20/0.44  fof(f50,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.20/0.44    inference(cnf_transformation,[],[f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.44    inference(nnf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.44  fof(f84,plain,(
% 0.20/0.44    ( ! [X0] : (r1_xboole_0(sK1,k4_xboole_0(X0,sK2))) )),
% 0.20/0.44    inference(resolution,[],[f58,f35])).
% 0.20/0.44  fof(f35,plain,(
% 0.20/0.44    r1_tarski(sK1,sK2)),
% 0.20/0.44    inference(cnf_transformation,[],[f24])).
% 0.20/0.44  fof(f58,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f20])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.44    inference(ennf_transformation,[],[f6])).
% 0.20/0.44  fof(f6,axiom,(
% 0.20/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.20/0.45  fof(f167,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.45    inference(superposition,[],[f80,f109])).
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)),
% 0.20/0.45    inference(resolution,[],[f46,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.45    inference(resolution,[],[f57,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    r1_tarski(sK1,k3_subset_1(sK0,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f24])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (26024)------------------------------
% 0.20/0.45  % (26024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (26024)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (26024)Memory used [KB]: 10746
% 0.20/0.45  % (26024)Time elapsed: 0.044 s
% 0.20/0.45  % (26024)------------------------------
% 0.20/0.45  % (26024)------------------------------
% 0.20/0.45  % (26013)Success in time 0.09 s
%------------------------------------------------------------------------------
