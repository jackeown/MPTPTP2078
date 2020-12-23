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
% DateTime   : Thu Dec  3 12:45:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 129 expanded)
%              Number of leaves         :    8 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :  128 ( 765 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f22])).

fof(f22,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
    & r1_xboole_0(sK3,sK2)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(X1,k3_subset_1(X0,X3))
                & r1_xboole_0(X3,X2)
                & r1_tarski(X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
              & r1_xboole_0(X3,X2)
              & r1_tarski(sK1,X2)
              & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
            & r1_xboole_0(X3,X2)
            & r1_tarski(sK1,X2)
            & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ? [X3] :
          ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
          & r1_xboole_0(X3,sK2)
          & r1_tarski(sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ~ r1_tarski(sK1,k3_subset_1(sK0,X3))
        & r1_xboole_0(X3,sK2)
        & r1_tarski(sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,k3_subset_1(sK0,sK3))
      & r1_xboole_0(sK3,sK2)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).

fof(f102,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(superposition,[],[f45,f97])).

fof(f97,plain,(
    sK2 = k4_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f83,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f83,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f20,f21,f71,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f71,plain,(
    r1_tarski(sK2,k3_subset_1(sK0,sK3)) ),
    inference(unit_resulting_resolution,[],[f21,f20,f42,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

fof(f42,plain,(
    r1_tarski(sK3,k3_subset_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f23,f21,f20,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f23,plain,(
    r1_xboole_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] : ~ r1_tarski(sK1,k4_xboole_0(X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f43,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f43,plain,(
    ~ r1_xboole_0(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f19,f21,f24,f26])).

fof(f24,plain,(
    ~ r1_tarski(sK1,k3_subset_1(sK0,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (11848)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (11843)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.42  % (11843)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(subsumption_resolution,[],[f102,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    r1_tarski(sK1,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ((~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f8,f15,f14,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X2] : (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(sK1,X2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ? [X3] : (~r1_tarski(sK1,k3_subset_1(sK0,X3)) & r1_xboole_0(X3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,k3_subset_1(sK0,sK3)) & r1_xboole_0(sK3,sK2) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(X1,k3_subset_1(X0,X3)) & r1_xboole_0(X3,X2) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(X1,k3_subset_1(X0,X3)) & (r1_xboole_0(X3,X2) & r1_tarski(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => ((r1_xboole_0(X3,X2) & r1_tarski(X1,X2)) => r1_tarski(X1,k3_subset_1(X0,X3))))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_subset_1)).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ~r1_tarski(sK1,sK2)),
% 0.21/0.42    inference(superposition,[],[f45,f97])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    sK2 = k4_xboole_0(sK2,sK3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f83,f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    r1_xboole_0(sK2,sK3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f20,f21,f71,f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (((r1_xboole_0(X1,X2) | ~r1_tarski(X1,k3_subset_1(X0,X2))) & (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(nnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    r1_tarski(sK2,k3_subset_1(sK0,sK3))),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f21,f20,f42,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_tarski(X2,k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    r1_tarski(sK3,k3_subset_1(sK0,sK2))),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f23,f21,f20,f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    r1_xboole_0(sK3,sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK1,k4_xboole_0(X0,sK3))) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f43,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ~r1_xboole_0(sK1,sK3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f19,f21,f24,f26])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ~r1_tarski(sK1,k3_subset_1(sK0,sK3))),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (11843)------------------------------
% 0.21/0.42  % (11843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (11843)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (11843)Memory used [KB]: 6140
% 0.21/0.42  % (11843)Time elapsed: 0.007 s
% 0.21/0.42  % (11843)------------------------------
% 0.21/0.42  % (11843)------------------------------
% 0.21/0.43  % (11840)Success in time 0.067 s
%------------------------------------------------------------------------------
