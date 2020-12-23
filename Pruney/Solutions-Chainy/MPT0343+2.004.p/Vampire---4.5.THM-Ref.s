%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  81 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   12
%              Number of atoms          :  117 ( 281 expanded)
%              Number of equality atoms :    9 (  25 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(subsumption_resolution,[],[f81,f16])).

fof(f16,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f81,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f80,f73])).

fof(f73,plain,(
    r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f70,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f42,f53])).

fof(f53,plain,(
    ! [X1] :
      ( r2_hidden(sK4(sK2,X1),sK0)
      | r1_tarski(sK2,X1) ) ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f24,f15])).

fof(f15,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK2,X0),sK0)
      | r2_hidden(sK4(sK2,X0),sK1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f29,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f13,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f22,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f13,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f80,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(resolution,[],[f78,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f76,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f49,f29])).

fof(f49,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f24,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f76,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK4(sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK4(sK1,sK2),sK0)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(X1,sK2),sK1)
      | r1_tarski(X1,sK2)
      | ~ r2_hidden(sK4(X1,sK2),sK0) ) ),
    inference(resolution,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f14,f33])).

fof(f14,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (26715)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.50  % (26723)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (26715)Refutation not found, incomplete strategy% (26715)------------------------------
% 0.20/0.50  % (26715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26717)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (26715)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26715)Memory used [KB]: 10746
% 0.20/0.51  % (26715)Time elapsed: 0.085 s
% 0.20/0.51  % (26715)------------------------------
% 0.20/0.51  % (26715)------------------------------
% 0.20/0.51  % (26709)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (26698)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (26701)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (26701)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f81,f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    sK1 != sK2),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    sK1 = sK2),
% 0.20/0.52    inference(subsumption_resolution,[],[f80,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    r1_tarski(sK2,sK1)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.20/0.52    inference(resolution,[],[f70,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0) | r1_tarski(sK2,X0)) )),
% 0.20/0.52    inference(resolution,[],[f42,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X1] : (r2_hidden(sK4(sK2,X1),sK0) | r1_tarski(sK2,X1)) )),
% 0.20/0.52    inference(resolution,[],[f48,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f24,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),sK0) | r2_hidden(sK4(sK2,X0),sK1) | r1_tarski(sK2,X0)) )),
% 0.20/0.52    inference(resolution,[],[f29,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f13,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f22,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ~r1_tarski(sK2,sK1) | sK1 = sK2),
% 0.20/0.52    inference(resolution,[],[f78,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f76,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 0.20/0.52    inference(resolution,[],[f49,f29])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f24,f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2) | ~r2_hidden(sK4(sK1,sK2),sK0)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    r1_tarski(sK1,sK2) | ~r2_hidden(sK4(sK1,sK2),sK0) | r1_tarski(sK1,sK2)),
% 0.20/0.52    inference(resolution,[],[f44,f29])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X1] : (~r2_hidden(sK4(X1,sK2),sK1) | r1_tarski(X1,sK2) | ~r2_hidden(sK4(X1,sK2),sK0)) )),
% 0.20/0.52    inference(resolution,[],[f30,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) )),
% 0.20/0.52    inference(resolution,[],[f14,f33])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (26701)------------------------------
% 0.20/0.52  % (26701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26701)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (26701)Memory used [KB]: 6268
% 0.20/0.52  % (26701)Time elapsed: 0.075 s
% 0.20/0.52  % (26701)------------------------------
% 0.20/0.52  % (26701)------------------------------
% 0.20/0.53  % (26691)Success in time 0.163 s
%------------------------------------------------------------------------------
