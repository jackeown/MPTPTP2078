%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:19 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   34 (  56 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 231 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(subsumption_resolution,[],[f82,f77])).

fof(f77,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f70,f14])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(X1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( ( r1_xboole_0(X3,X2)
                    & r1_tarski(X1,X2) )
                 => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(X0,sK3) ) ),
    inference(superposition,[],[f27,f66])).

fof(f66,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f62,f15])).

fof(f15,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X3,X4)
      | k4_xboole_0(X4,X3) = X4 ) ),
    inference(resolution,[],[f60,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,X0) ) ),
    inference(resolution,[],[f34,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f34,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK4(X3,X4),X5)
      | ~ r1_xboole_0(X4,X5)
      | r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f19,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f82,plain,(
    ~ r1_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f81,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f81,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f78,f13])).

fof(f13,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f78,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : run_vampire %s %d
% 0.07/0.26  % Computer   : n023.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 16:47:50 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.12/0.30  % (1201)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.12/0.30  % (1196)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.12/0.30  % (1202)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.12/0.30  % (1203)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.12/0.30  % (1196)Refutation found. Thanks to Tanya!
% 0.12/0.30  % SZS status Theorem for theBenchmark
% 0.12/0.30  % SZS output start Proof for theBenchmark
% 0.12/0.30  fof(f83,plain,(
% 0.12/0.30    $false),
% 0.12/0.30    inference(subsumption_resolution,[],[f82,f77])).
% 0.12/0.30  fof(f77,plain,(
% 0.12/0.30    r1_xboole_0(sK1,sK3)),
% 0.12/0.30    inference(resolution,[],[f70,f14])).
% 0.12/0.30  fof(f14,plain,(
% 0.12/0.30    r1_tarski(sK1,sK2)),
% 0.12/0.30    inference(cnf_transformation,[],[f9])).
% 0.12/0.30  fof(f9,plain,(
% 0.12/0.30    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.30    inference(flattening,[],[f8])).
% 0.12/0.30  fof(f8,plain,(
% 0.12/0.30    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.30    inference(ennf_transformation,[],[f6])).
% 0.12/0.30  fof(f6,negated_conjecture,(
% 0.12/0.30    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.12/0.30    inference(negated_conjecture,[],[f5])).
% 0.12/0.30  fof(f5,conjecture,(
% 0.12/0.30    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.12/0.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).
% 0.12/0.30  fof(f70,plain,(
% 0.12/0.30    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK3)) )),
% 0.12/0.30    inference(superposition,[],[f27,f66])).
% 0.12/0.30  fof(f66,plain,(
% 0.12/0.30    sK2 = k4_xboole_0(sK2,sK3)),
% 0.12/0.30    inference(resolution,[],[f62,f15])).
% 0.12/0.30  fof(f15,plain,(
% 0.12/0.30    r1_xboole_0(sK3,sK2)),
% 0.12/0.30    inference(cnf_transformation,[],[f9])).
% 0.12/0.30  fof(f62,plain,(
% 0.12/0.30    ( ! [X4,X3] : (~r1_xboole_0(X3,X4) | k4_xboole_0(X4,X3) = X4) )),
% 0.12/0.30    inference(resolution,[],[f60,f25])).
% 0.12/0.30  fof(f25,plain,(
% 0.12/0.30    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.12/0.30    inference(cnf_transformation,[],[f3])).
% 0.12/0.30  fof(f3,axiom,(
% 0.12/0.30    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.12/0.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.12/0.30  fof(f60,plain,(
% 0.12/0.30    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.12/0.30    inference(duplicate_literal_removal,[],[f57])).
% 0.12/0.30  fof(f57,plain,(
% 0.12/0.30    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) | r1_xboole_0(X1,X0)) )),
% 0.12/0.30    inference(resolution,[],[f34,f20])).
% 0.12/0.30  fof(f20,plain,(
% 0.12/0.30    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.12/0.30    inference(cnf_transformation,[],[f10])).
% 0.12/0.30  fof(f10,plain,(
% 0.12/0.30    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.12/0.30    inference(ennf_transformation,[],[f7])).
% 0.12/0.30  fof(f7,plain,(
% 0.12/0.30    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.12/0.30    inference(rectify,[],[f1])).
% 0.12/0.30  fof(f1,axiom,(
% 0.12/0.30    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.12/0.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.12/0.30  fof(f34,plain,(
% 0.12/0.30    ( ! [X4,X5,X3] : (~r2_hidden(sK4(X3,X4),X5) | ~r1_xboole_0(X4,X5) | r1_xboole_0(X3,X4)) )),
% 0.12/0.30    inference(resolution,[],[f19,f21])).
% 0.12/0.30  fof(f21,plain,(
% 0.12/0.30    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.12/0.30    inference(cnf_transformation,[],[f10])).
% 0.12/0.30  fof(f19,plain,(
% 0.12/0.30    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.12/0.30    inference(cnf_transformation,[],[f10])).
% 0.12/0.30  fof(f27,plain,(
% 0.12/0.30    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.12/0.30    inference(cnf_transformation,[],[f12])).
% 0.12/0.30  fof(f12,plain,(
% 0.12/0.30    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.12/0.30    inference(ennf_transformation,[],[f2])).
% 0.12/0.30  fof(f2,axiom,(
% 0.12/0.30    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.12/0.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.12/0.30  fof(f82,plain,(
% 0.12/0.30    ~r1_xboole_0(sK1,sK3)),
% 0.12/0.30    inference(subsumption_resolution,[],[f81,f18])).
% 0.12/0.30  fof(f18,plain,(
% 0.12/0.30    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.12/0.30    inference(cnf_transformation,[],[f9])).
% 0.12/0.30  fof(f81,plain,(
% 0.12/0.30    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,sK3)),
% 0.12/0.30    inference(subsumption_resolution,[],[f78,f13])).
% 0.12/0.30  fof(f13,plain,(
% 0.12/0.30    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.12/0.30    inference(cnf_transformation,[],[f9])).
% 0.12/0.30  fof(f78,plain,(
% 0.12/0.30    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~r1_xboole_0(sK1,sK3)),
% 0.12/0.30    inference(resolution,[],[f23,f16])).
% 0.12/0.30  fof(f16,plain,(
% 0.12/0.30    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.12/0.30    inference(cnf_transformation,[],[f9])).
% 0.12/0.30  fof(f23,plain,(
% 0.12/0.30    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_xboole_0(X1,X2)) )),
% 0.12/0.30    inference(cnf_transformation,[],[f11])).
% 0.12/0.30  fof(f11,plain,(
% 0.12/0.30    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.12/0.30    inference(ennf_transformation,[],[f4])).
% 0.12/0.30  fof(f4,axiom,(
% 0.12/0.30    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.12/0.30    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).
% 0.12/0.30  % SZS output end Proof for theBenchmark
% 0.12/0.30  % (1196)------------------------------
% 0.12/0.30  % (1196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.30  % (1196)Termination reason: Refutation
% 0.12/0.30  
% 0.12/0.30  % (1196)Memory used [KB]: 10618
% 0.12/0.30  % (1196)Time elapsed: 0.004 s
% 0.12/0.30  % (1196)------------------------------
% 0.12/0.30  % (1196)------------------------------
% 0.12/0.30  % (1194)Success in time 0.034 s
%------------------------------------------------------------------------------
