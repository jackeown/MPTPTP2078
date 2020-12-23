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
% DateTime   : Thu Dec  3 12:46:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 159 expanded)
%              Number of leaves         :    6 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  114 ( 768 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(global_subsumption,[],[f17,f43])).

fof(f43,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f42,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f42,plain,(
    ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(global_subsumption,[],[f16,f38,f41])).

fof(f41,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(superposition,[],[f39,f24])).

fof(f24,plain,(
    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2)) ),
    inference(resolution,[],[f20,f17])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ r1_tarski(k7_setfam_1(X0,sK1),k7_setfam_1(X0,k7_setfam_1(sK0,sK2)))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f37,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ~ r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).

fof(f37,plain,(
    ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f16,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f35,f21])).

fof(f35,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    inference(global_subsumption,[],[f17,f34])).

fof(f34,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(duplicate_literal_removal,[],[f33])).

fof(f33,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    inference(superposition,[],[f31,f23])).

fof(f23,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f20,f16])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(k7_setfam_1(X0,k7_setfam_1(sK0,sK1)),k7_setfam_1(X0,sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ) ),
    inference(resolution,[],[f22,f19])).

fof(f19,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2)
    | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
      | r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | r1_tarski(k7_setfam_1(X0,X1),X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | ~ r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & ( r1_tarski(sK1,k7_setfam_1(sK0,X2))
            | r1_tarski(k7_setfam_1(sK0,sK1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,X2))
          | ~ r1_tarski(k7_setfam_1(sK0,sK1),X2) )
        & ( r1_tarski(sK1,k7_setfam_1(sK0,X2))
          | r1_tarski(k7_setfam_1(sK0,sK1),X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK2))
        | ~ r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
      & ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
        | r1_tarski(k7_setfam_1(sK0,sK1),sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k7_setfam_1(X0,X2))
            | ~ r1_tarski(k7_setfam_1(X0,X1),X2) )
          & ( r1_tarski(X1,k7_setfam_1(X0,X2))
            | r1_tarski(k7_setfam_1(X0,X1),X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <~> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(k7_setfam_1(X0,X1),X2)
            <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f38,plain,(
    r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f37,f18])).

fof(f18,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK2))
    | r1_tarski(k7_setfam_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.39  % (15278)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (15275)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (15275)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(global_subsumption,[],[f17,f43])).
% 0.20/0.41  fof(f43,plain,(
% 0.20/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(resolution,[],[f42,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f8])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    ~m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(global_subsumption,[],[f16,f38,f41])).
% 0.20/0.41  fof(f41,plain,(
% 0.20/0.41    ~r1_tarski(k7_setfam_1(sK0,sK1),sK2) | ~m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(superposition,[],[f39,f24])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    sK2 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK2))),
% 0.20/0.41    inference(resolution,[],[f20,f17])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.20/0.41    inference(cnf_transformation,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(k7_setfam_1(X0,sK1),k7_setfam_1(X0,k7_setfam_1(sK0,sK2))) | ~m1_subset_1(k7_setfam_1(sK0,sK2),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.41    inference(resolution,[],[f37,f22])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(flattening,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ~r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),k7_setfam_1(X0,X2)) => r1_tarski(X1,X2))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_setfam_1)).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k7_setfam_1(sK0,sK2))),
% 0.20/0.41    inference(global_subsumption,[],[f16,f36])).
% 0.20/0.41  fof(f36,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(resolution,[],[f35,f21])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r1_tarski(sK1,k7_setfam_1(sK0,sK2))),
% 0.20/0.41    inference(global_subsumption,[],[f17,f34])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(duplicate_literal_removal,[],[f33])).
% 0.20/0.41  fof(f33,plain,(
% 0.20/0.41    ~r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~r1_tarski(sK1,k7_setfam_1(sK0,sK2))),
% 0.20/0.41    inference(superposition,[],[f31,f23])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.20/0.41    inference(resolution,[],[f20,f16])).
% 0.20/0.41  fof(f31,plain,(
% 0.20/0.41    ( ! [X0] : (~r1_tarski(k7_setfam_1(X0,k7_setfam_1(sK0,sK1)),k7_setfam_1(X0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r1_tarski(sK1,k7_setfam_1(sK0,sK2))) )),
% 0.20/0.41    inference(resolution,[],[f22,f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    ~r1_tarski(k7_setfam_1(sK0,sK1),sK2) | ~r1_tarski(sK1,k7_setfam_1(sK0,sK2))),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ((~r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | ~r1_tarski(k7_setfam_1(sK0,sK1),sK2)) & (r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | r1_tarski(k7_setfam_1(sK0,sK1),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14,f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2)) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | r1_tarski(k7_setfam_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : ((~r1_tarski(sK1,k7_setfam_1(sK0,X2)) | ~r1_tarski(k7_setfam_1(sK0,sK1),X2)) & (r1_tarski(sK1,k7_setfam_1(sK0,X2)) | r1_tarski(k7_setfam_1(sK0,sK1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ? [X2] : ((~r1_tarski(sK1,k7_setfam_1(sK0,X2)) | ~r1_tarski(k7_setfam_1(sK0,sK1),X2)) & (r1_tarski(sK1,k7_setfam_1(sK0,X2)) | r1_tarski(k7_setfam_1(sK0,sK1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => ((~r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | ~r1_tarski(k7_setfam_1(sK0,sK1),sK2)) & (r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | r1_tarski(k7_setfam_1(sK0,sK1),sK2)) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2)) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | r1_tarski(k7_setfam_1(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(flattening,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : (((~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2)) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | r1_tarski(k7_setfam_1(X0,X1),X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(nnf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,plain,(
% 0.20/0.41    ? [X0,X1] : (? [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <~> r1_tarski(X1,k7_setfam_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.41    inference(ennf_transformation,[],[f5])).
% 0.20/0.41  fof(f5,negated_conjecture,(
% 0.20/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 0.20/0.41    inference(negated_conjecture,[],[f4])).
% 0.20/0.41  fof(f4,conjecture,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 0.20/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).
% 0.20/0.41  fof(f38,plain,(
% 0.20/0.41    r1_tarski(k7_setfam_1(sK0,sK1),sK2)),
% 0.20/0.41    inference(resolution,[],[f37,f18])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    r1_tarski(sK1,k7_setfam_1(sK0,sK2)) | r1_tarski(k7_setfam_1(sK0,sK1),sK2)),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.41    inference(cnf_transformation,[],[f15])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (15275)------------------------------
% 0.20/0.41  % (15275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (15275)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (15275)Memory used [KB]: 6140
% 0.20/0.41  % (15275)Time elapsed: 0.006 s
% 0.20/0.41  % (15275)------------------------------
% 0.20/0.41  % (15275)------------------------------
% 0.20/0.42  % (15270)Success in time 0.062 s
%------------------------------------------------------------------------------
