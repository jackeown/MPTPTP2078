%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:07 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 155 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f22,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(subsumption_resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X1),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X0) ) ),
    inference(resolution,[],[f38,f22])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k3_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
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

fof(f81,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f49,f53])).

fof(f53,plain,(
    ! [X2] : k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2)) ),
    inference(resolution,[],[f51,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f50,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

fof(f50,plain,(
    ! [X0] :
      ( m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    inference(superposition,[],[f23,f46])).

fof(f46,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(resolution,[],[f24,f16])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f49,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f42,f46])).

fof(f42,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(backward_demodulation,[],[f17,f41])).

fof(f41,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f19,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:05:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (3893)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (3892)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.16/0.51  % (3895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.16/0.52  % (3921)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.16/0.52  % (3896)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.16/0.52  % (3909)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.16/0.53  % (3911)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.16/0.53  % (3897)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.16/0.53  % (3897)Refutation found. Thanks to Tanya!
% 1.16/0.53  % SZS status Theorem for theBenchmark
% 1.16/0.53  % SZS output start Proof for theBenchmark
% 1.16/0.53  fof(f84,plain,(
% 1.16/0.53    $false),
% 1.16/0.53    inference(subsumption_resolution,[],[f83,f36])).
% 1.16/0.53  fof(f36,plain,(
% 1.16/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.16/0.53    inference(duplicate_literal_removal,[],[f35])).
% 1.16/0.53  fof(f35,plain,(
% 1.16/0.53    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.16/0.53    inference(resolution,[],[f22,f21])).
% 1.16/0.53  fof(f21,plain,(
% 1.16/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f11])).
% 1.16/0.53  fof(f11,plain,(
% 1.16/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.16/0.53    inference(ennf_transformation,[],[f1])).
% 1.16/0.53  fof(f1,axiom,(
% 1.16/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.16/0.53  fof(f22,plain,(
% 1.16/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f11])).
% 1.16/0.53  fof(f83,plain,(
% 1.16/0.53    ~r1_tarski(sK0,sK0)),
% 1.16/0.53    inference(subsumption_resolution,[],[f81,f79])).
% 1.16/0.53  fof(f79,plain,(
% 1.16/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.16/0.53    inference(duplicate_literal_removal,[],[f74])).
% 1.16/0.53  fof(f74,plain,(
% 1.16/0.53    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0) | r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.16/0.53    inference(resolution,[],[f38,f22])).
% 1.16/0.53  fof(f38,plain,(
% 1.16/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK3(k3_xboole_0(X0,X1),X2),X0) | r1_tarski(k3_xboole_0(X0,X1),X2)) )),
% 1.16/0.53    inference(resolution,[],[f34,f21])).
% 1.16/0.53  fof(f34,plain,(
% 1.16/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X0)) )),
% 1.16/0.53    inference(equality_resolution,[],[f28])).
% 1.16/0.53  fof(f28,plain,(
% 1.16/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.16/0.53    inference(cnf_transformation,[],[f2])).
% 1.16/0.53  fof(f2,axiom,(
% 1.16/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.16/0.53  fof(f81,plain,(
% 1.16/0.53    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | ~r1_tarski(sK0,sK0)),
% 1.16/0.53    inference(resolution,[],[f31,f54])).
% 1.16/0.53  fof(f54,plain,(
% 1.16/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k3_xboole_0(sK1,sK2)))),
% 1.16/0.53    inference(backward_demodulation,[],[f49,f53])).
% 1.16/0.53  fof(f53,plain,(
% 1.16/0.53    ( ! [X2] : (k3_subset_1(sK0,k3_xboole_0(X2,sK2)) = k4_xboole_0(sK0,k3_xboole_0(X2,sK2))) )),
% 1.16/0.53    inference(resolution,[],[f51,f19])).
% 1.16/0.53  fof(f19,plain,(
% 1.16/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f10])).
% 1.16/0.53  fof(f10,plain,(
% 1.16/0.53    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.53    inference(ennf_transformation,[],[f4])).
% 1.16/0.53  fof(f4,axiom,(
% 1.16/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.16/0.53  fof(f51,plain,(
% 1.16/0.53    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))) )),
% 1.16/0.53    inference(subsumption_resolution,[],[f50,f16])).
% 1.16/0.53  fof(f16,plain,(
% 1.16/0.53    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.16/0.53    inference(cnf_transformation,[],[f9])).
% 1.16/0.53  fof(f9,plain,(
% 1.16/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.16/0.53    inference(ennf_transformation,[],[f8])).
% 1.16/0.53  fof(f8,negated_conjecture,(
% 1.16/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.16/0.53    inference(negated_conjecture,[],[f7])).
% 1.16/0.53  fof(f7,conjecture,(
% 1.16/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,X1),k3_subset_1(X0,k9_subset_1(X0,X1,X2)))))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).
% 1.16/0.53  fof(f50,plain,(
% 1.16/0.53    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0))) )),
% 1.16/0.53    inference(superposition,[],[f23,f46])).
% 1.16/0.53  fof(f46,plain,(
% 1.16/0.53    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) )),
% 1.16/0.53    inference(resolution,[],[f24,f16])).
% 1.16/0.53  fof(f24,plain,(
% 1.16/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f13])).
% 1.16/0.53  fof(f13,plain,(
% 1.16/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.16/0.53    inference(ennf_transformation,[],[f6])).
% 1.16/0.53  fof(f6,axiom,(
% 1.16/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.16/0.53  fof(f23,plain,(
% 1.16/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.16/0.53    inference(cnf_transformation,[],[f12])).
% 1.16/0.53  fof(f12,plain,(
% 1.16/0.53    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.16/0.53    inference(ennf_transformation,[],[f5])).
% 1.16/0.53  fof(f5,axiom,(
% 1.16/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.16/0.53  fof(f49,plain,(
% 1.16/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k3_xboole_0(sK1,sK2)))),
% 1.16/0.53    inference(backward_demodulation,[],[f42,f46])).
% 1.16/0.53  fof(f42,plain,(
% 1.16/0.53    ~r1_tarski(k4_xboole_0(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.16/0.53    inference(backward_demodulation,[],[f17,f41])).
% 1.16/0.53  fof(f41,plain,(
% 1.16/0.53    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 1.16/0.53    inference(resolution,[],[f19,f18])).
% 1.16/0.53  fof(f18,plain,(
% 1.16/0.53    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.16/0.53    inference(cnf_transformation,[],[f9])).
% 1.16/0.53  fof(f17,plain,(
% 1.16/0.53    ~r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k9_subset_1(sK0,sK1,sK2)))),
% 1.16/0.53    inference(cnf_transformation,[],[f9])).
% 1.16/0.53  fof(f31,plain,(
% 1.16/0.53    ( ! [X2,X0,X3,X1] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.16/0.53    inference(cnf_transformation,[],[f15])).
% 1.16/0.53  fof(f15,plain,(
% 1.16/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.16/0.53    inference(flattening,[],[f14])).
% 1.16/0.53  fof(f14,plain,(
% 1.16/0.53    ! [X0,X1,X2,X3] : (r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.16/0.53    inference(ennf_transformation,[],[f3])).
% 1.16/0.53  fof(f3,axiom,(
% 1.16/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)))),
% 1.16/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_xboole_1)).
% 1.16/0.53  % SZS output end Proof for theBenchmark
% 1.16/0.53  % (3897)------------------------------
% 1.16/0.53  % (3897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (3897)Termination reason: Refutation
% 1.16/0.53  
% 1.16/0.53  % (3897)Memory used [KB]: 6268
% 1.16/0.53  % (3897)Time elapsed: 0.107 s
% 1.16/0.53  % (3897)------------------------------
% 1.16/0.53  % (3897)------------------------------
% 1.16/0.53  % (3891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.16/0.53  % (3890)Success in time 0.165 s
%------------------------------------------------------------------------------
