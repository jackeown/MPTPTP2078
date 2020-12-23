%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:49 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 (  70 expanded)
%              Number of leaves         :    7 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 291 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(global_subsumption,[],[f33,f42])).

fof(f42,plain,(
    r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f40,f20])).

fof(f20,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ v3_setfam_1(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v3_setfam_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ v3_setfam_1(X2,X0)
            & r1_tarski(X2,X1)
            & v3_setfam_1(X1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ v3_setfam_1(X2,sK0)
          & r1_tarski(X2,sK1)
          & v3_setfam_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ v3_setfam_1(X2,sK0)
        & r1_tarski(X2,sK1)
        & v3_setfam_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ v3_setfam_1(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & v3_setfam_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ v3_setfam_1(X2,X0)
          & r1_tarski(X2,X1)
          & v3_setfam_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ( r1_tarski(X2,X1)
                & v3_setfam_1(X1,X0) )
             => v3_setfam_1(X2,X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ( r1_tarski(X2,X1)
              & v3_setfam_1(X1,X0) )
           => v3_setfam_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,X0)
      | r2_hidden(sK0,X0) ) ),
    inference(resolution,[],[f39,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f39,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(sK0),X0)
      | ~ r1_tarski(sK2,X0) ) ),
    inference(superposition,[],[f27,f38])).

fof(f38,plain,(
    sK2 = k2_xboole_0(k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    r2_hidden(sK0,sK2) ),
    inference(global_subsumption,[],[f21,f35])).

fof(f35,plain,
    ( r2_hidden(sK0,sK2)
    | v3_setfam_1(sK2,sK0) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | r2_hidden(X0,X1)
      | v3_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( v3_setfam_1(X1,X0)
          | r2_hidden(X0,X1) )
        & ( ~ r2_hidden(X0,X1)
          | ~ v3_setfam_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( v3_setfam_1(X1,X0)
      <=> ~ r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).

fof(f21,plain,(
    ~ v3_setfam_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f33,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(global_subsumption,[],[f19,f31])).

fof(f31,plain,
    ( ~ v3_setfam_1(sK1,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f23,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ v3_setfam_1(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    v3_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:11:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.40  % (8385)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.12/0.41  % (8385)Refutation found. Thanks to Tanya!
% 0.12/0.41  % SZS status Theorem for theBenchmark
% 0.12/0.41  % SZS output start Proof for theBenchmark
% 0.12/0.41  fof(f43,plain,(
% 0.12/0.41    $false),
% 0.12/0.41    inference(global_subsumption,[],[f33,f42])).
% 0.12/0.41  fof(f42,plain,(
% 0.12/0.41    r2_hidden(sK0,sK1)),
% 0.12/0.41    inference(resolution,[],[f40,f20])).
% 0.12/0.41  fof(f20,plain,(
% 0.12/0.41    r1_tarski(sK2,sK1)),
% 0.12/0.41    inference(cnf_transformation,[],[f14])).
% 0.12/0.41  fof(f14,plain,(
% 0.12/0.41    (~v3_setfam_1(sK2,sK0) & r1_tarski(sK2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.12/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13,f12])).
% 0.12/0.41  fof(f12,plain,(
% 0.12/0.41    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~v3_setfam_1(X2,sK0) & r1_tarski(X2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.12/0.41    introduced(choice_axiom,[])).
% 0.12/0.41  fof(f13,plain,(
% 0.12/0.41    ? [X2] : (~v3_setfam_1(X2,sK0) & r1_tarski(X2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~v3_setfam_1(sK2,sK0) & r1_tarski(sK2,sK1) & v3_setfam_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.12/0.41    introduced(choice_axiom,[])).
% 0.12/0.41  fof(f8,plain,(
% 0.12/0.41    ? [X0,X1] : (? [X2] : (~v3_setfam_1(X2,X0) & r1_tarski(X2,X1) & v3_setfam_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.12/0.41    inference(flattening,[],[f7])).
% 0.12/0.41  fof(f7,plain,(
% 0.12/0.41    ? [X0,X1] : (? [X2] : ((~v3_setfam_1(X2,X0) & (r1_tarski(X2,X1) & v3_setfam_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.12/0.41    inference(ennf_transformation,[],[f6])).
% 0.12/0.41  fof(f6,negated_conjecture,(
% 0.12/0.41    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.12/0.41    inference(negated_conjecture,[],[f5])).
% 0.12/0.41  fof(f5,conjecture,(
% 0.12/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((r1_tarski(X2,X1) & v3_setfam_1(X1,X0)) => v3_setfam_1(X2,X0))))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_setfam_1)).
% 0.12/0.41  fof(f40,plain,(
% 0.12/0.41    ( ! [X0] : (~r1_tarski(sK2,X0) | r2_hidden(sK0,X0)) )),
% 0.12/0.41    inference(resolution,[],[f39,f25])).
% 0.12/0.41  fof(f25,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f16])).
% 0.12/0.41  fof(f16,plain,(
% 0.12/0.41    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.12/0.41    inference(nnf_transformation,[],[f3])).
% 0.12/0.41  fof(f3,axiom,(
% 0.12/0.41    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.12/0.41  fof(f39,plain,(
% 0.12/0.41    ( ! [X0] : (r1_tarski(k1_tarski(sK0),X0) | ~r1_tarski(sK2,X0)) )),
% 0.12/0.41    inference(superposition,[],[f27,f38])).
% 0.12/0.41  fof(f38,plain,(
% 0.12/0.41    sK2 = k2_xboole_0(k1_tarski(sK0),sK2)),
% 0.12/0.41    inference(resolution,[],[f30,f36])).
% 0.12/0.41  fof(f36,plain,(
% 0.12/0.41    r2_hidden(sK0,sK2)),
% 0.12/0.41    inference(global_subsumption,[],[f21,f35])).
% 0.12/0.41  fof(f35,plain,(
% 0.12/0.41    r2_hidden(sK0,sK2) | v3_setfam_1(sK2,sK0)),
% 0.12/0.41    inference(resolution,[],[f24,f18])).
% 0.12/0.41  fof(f18,plain,(
% 0.12/0.41    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.12/0.41    inference(cnf_transformation,[],[f14])).
% 0.12/0.41  fof(f24,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | r2_hidden(X0,X1) | v3_setfam_1(X1,X0)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f15])).
% 0.12/0.41  fof(f15,plain,(
% 0.12/0.41    ! [X0,X1] : (((v3_setfam_1(X1,X0) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | ~v3_setfam_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.12/0.41    inference(nnf_transformation,[],[f10])).
% 0.12/0.41  fof(f10,plain,(
% 0.12/0.41    ! [X0,X1] : ((v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.12/0.41    inference(ennf_transformation,[],[f4])).
% 0.12/0.41  fof(f4,axiom,(
% 0.12/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (v3_setfam_1(X1,X0) <=> ~r2_hidden(X0,X1)))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_setfam_1)).
% 0.12/0.41  fof(f21,plain,(
% 0.12/0.41    ~v3_setfam_1(sK2,sK0)),
% 0.12/0.41    inference(cnf_transformation,[],[f14])).
% 0.12/0.41  fof(f30,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1) )),
% 0.12/0.41    inference(resolution,[],[f22,f26])).
% 0.12/0.41  fof(f26,plain,(
% 0.12/0.41    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f16])).
% 0.12/0.41  fof(f22,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.12/0.41    inference(cnf_transformation,[],[f9])).
% 0.12/0.41  fof(f9,plain,(
% 0.12/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.12/0.41    inference(ennf_transformation,[],[f2])).
% 0.12/0.41  fof(f2,axiom,(
% 0.12/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.12/0.41  fof(f27,plain,(
% 0.12/0.41    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f11])).
% 0.12/0.41  fof(f11,plain,(
% 0.12/0.41    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.12/0.41    inference(ennf_transformation,[],[f1])).
% 0.12/0.41  fof(f1,axiom,(
% 0.12/0.41    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.12/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.12/0.41  fof(f33,plain,(
% 0.12/0.41    ~r2_hidden(sK0,sK1)),
% 0.12/0.41    inference(global_subsumption,[],[f19,f31])).
% 0.12/0.41  fof(f31,plain,(
% 0.12/0.41    ~v3_setfam_1(sK1,sK0) | ~r2_hidden(sK0,sK1)),
% 0.12/0.41    inference(resolution,[],[f23,f17])).
% 0.12/0.41  fof(f17,plain,(
% 0.12/0.41    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.12/0.41    inference(cnf_transformation,[],[f14])).
% 0.12/0.41  fof(f23,plain,(
% 0.12/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~v3_setfam_1(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.12/0.41    inference(cnf_transformation,[],[f15])).
% 0.12/0.41  fof(f19,plain,(
% 0.12/0.41    v3_setfam_1(sK1,sK0)),
% 0.12/0.41    inference(cnf_transformation,[],[f14])).
% 0.12/0.41  % SZS output end Proof for theBenchmark
% 0.12/0.41  % (8385)------------------------------
% 0.12/0.41  % (8385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.41  % (8385)Termination reason: Refutation
% 0.12/0.41  
% 0.12/0.41  % (8385)Memory used [KB]: 10618
% 0.12/0.41  % (8385)Time elapsed: 0.004 s
% 0.12/0.41  % (8385)------------------------------
% 0.12/0.41  % (8385)------------------------------
% 0.12/0.41  % (8373)Success in time 0.059 s
%------------------------------------------------------------------------------
