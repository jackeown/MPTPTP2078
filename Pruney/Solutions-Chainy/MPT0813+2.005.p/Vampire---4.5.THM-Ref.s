%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:09 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   28 (  72 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   75 ( 241 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f24,f33,f34,f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f12])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f34,plain,(
    r2_hidden(sK4(sK0,k2_zfmisc_1(sK1,sK2)),sK3) ),
    inference(unit_resulting_resolution,[],[f16,f32,f18])).

fof(f32,plain,(
    r2_hidden(sK4(sK0,k2_zfmisc_1(sK1,sK2)),sK0) ),
    inference(unit_resulting_resolution,[],[f28,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f17,plain,(
    ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & r1_tarski(sK0,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).

fof(f8,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & r1_tarski(X0,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
   => ( ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & r1_tarski(sK0,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & r1_tarski(X0,X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
       => ( r1_tarski(X0,X3)
         => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

fof(f16,plain,(
    r1_tarski(sK0,sK3) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,(
    ~ r2_hidden(sK4(sK0,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f15,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n025.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:31:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.39  % (23703)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.19/0.40  % (23703)Refutation found. Thanks to Tanya!
% 0.19/0.40  % SZS status Theorem for theBenchmark
% 0.19/0.41  % (23711)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f40,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f24,f33,f34,f18])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f13])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f11,f12])).
% 0.19/0.41  fof(f12,plain,(
% 0.19/0.41    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f11,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.41    inference(rectify,[],[f10])).
% 0.19/0.41  fof(f10,plain,(
% 0.19/0.41    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.41    inference(nnf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,plain,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.41  fof(f34,plain,(
% 0.19/0.41    r2_hidden(sK4(sK0,k2_zfmisc_1(sK1,sK2)),sK3)),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f16,f32,f18])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    r2_hidden(sK4(sK0,k2_zfmisc_1(sK1,sK2)),sK0)),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f28,f19])).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f13])).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    ~r1_tarski(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f17,f22])).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.41    inference(nnf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,plain,(
% 0.19/0.41    ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f6,f8])).
% 0.19/0.41  fof(f8,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) => (~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & r1_tarski(sK0,sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f6,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(X0,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.19/0.41    inference(flattening,[],[f5])).
% 0.19/0.41  fof(f5,plain,(
% 0.19/0.41    ? [X0,X1,X2,X3] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & r1_tarski(X0,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.19/0.41    inference(ennf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,negated_conjecture,(
% 0.19/0.41    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.19/0.41    inference(negated_conjecture,[],[f3])).
% 0.19/0.41  fof(f3,conjecture,(
% 0.19/0.41    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.19/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    r1_tarski(sK0,sK3)),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    ~r2_hidden(sK4(sK0,k2_zfmisc_1(sK1,sK2)),k2_zfmisc_1(sK1,sK2))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f28,f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f13])).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f15,f21])).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (23703)------------------------------
% 0.19/0.41  % (23703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (23703)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (23703)Memory used [KB]: 895
% 0.19/0.41  % (23703)Time elapsed: 0.028 s
% 0.19/0.41  % (23703)------------------------------
% 0.19/0.41  % (23703)------------------------------
% 0.19/0.41  % (23697)Success in time 0.067 s
%------------------------------------------------------------------------------
