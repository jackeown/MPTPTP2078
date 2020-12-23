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
% DateTime   : Thu Dec  3 13:08:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 307 expanded)
%              Number of leaves         :   10 (  82 expanded)
%              Depth                    :   21
%              Number of atoms          :  166 (1532 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(global_subsumption,[],[f27,f59,f94,f108])).

fof(f108,plain,(
    v1_finset_1(sK1) ),
    inference(resolution,[],[f103,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f69,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_tarski(sK0))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f68,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k3_tarski(sK0)))
      | v1_finset_1(X0) ) ),
    inference(global_subsumption,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( v1_finset_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k3_tarski(sK0))) ) ),
    inference(resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).

fof(f103,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f98,f59])).

fof(f98,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v1_finset_1(k3_tarski(sK0)) ),
    inference(resolution,[],[f94,f26])).

fof(f26,plain,
    ( ~ v1_finset_1(sK0)
    | r2_hidden(sK1,sK0)
    | ~ v1_finset_1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( ~ v1_finset_1(k3_tarski(sK0))
      | ( ~ v1_finset_1(sK1)
        & r2_hidden(sK1,sK0) )
      | ~ v1_finset_1(sK0) )
    & ( v1_finset_1(k3_tarski(sK0))
      | ( ! [X2] :
            ( v1_finset_1(X2)
            | ~ r2_hidden(X2,sK0) )
        & v1_finset_1(sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ( ~ v1_finset_1(k3_tarski(X0))
          | ? [X1] :
              ( ~ v1_finset_1(X1)
              & r2_hidden(X1,X0) )
          | ~ v1_finset_1(X0) )
        & ( v1_finset_1(k3_tarski(X0))
          | ( ! [X2] :
                ( v1_finset_1(X2)
                | ~ r2_hidden(X2,X0) )
            & v1_finset_1(X0) ) ) )
   => ( ( ~ v1_finset_1(k3_tarski(sK0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,sK0) )
        | ~ v1_finset_1(sK0) )
      & ( v1_finset_1(k3_tarski(sK0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,sK0) )
          & v1_finset_1(sK0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ~ v1_finset_1(X1)
        & r2_hidden(X1,sK0) )
   => ( ~ v1_finset_1(sK1)
      & r2_hidden(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X2] :
              ( v1_finset_1(X2)
              | ~ r2_hidden(X2,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ( ~ v1_finset_1(k3_tarski(X0))
        | ? [X1] :
            ( ~ v1_finset_1(X1)
            & r2_hidden(X1,X0) )
        | ~ v1_finset_1(X0) )
      & ( v1_finset_1(k3_tarski(X0))
        | ( ! [X1] :
              ( v1_finset_1(X1)
              | ~ r2_hidden(X1,X0) )
          & v1_finset_1(X0) ) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( ! [X1] :
            ( v1_finset_1(X1)
            | ~ r2_hidden(X1,X0) )
        & v1_finset_1(X0) )
    <~> v1_finset_1(k3_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( ! [X1] :
              ( r2_hidden(X1,X0)
             => v1_finset_1(X1) )
          & v1_finset_1(X0) )
      <=> v1_finset_1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
    <=> v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).

fof(f94,plain,(
    v1_finset_1(sK0) ),
    inference(resolution,[],[f93,f28])).

fof(f28,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f93,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(k3_tarski(sK0)))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f72,f35])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(sK0))))
      | v1_finset_1(X0) ) ),
    inference(resolution,[],[f67,f30])).

fof(f67,plain,(
    v1_finset_1(k1_zfmisc_1(k3_tarski(sK0))) ),
    inference(resolution,[],[f59,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_finset_1(k1_zfmisc_1(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => v1_finset_1(k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).

fof(f59,plain,(
    v1_finset_1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f24,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,
    ( v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ~ v1_finset_1(sK2(X0))
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f21])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
     => ( ~ v1_finset_1(sK2(X0))
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | ? [X1] :
          ( ~ v1_finset_1(X1)
          & r2_hidden(X1,X0) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v1_finset_1(X1) )
        & v1_finset_1(X0) )
     => v1_finset_1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).

fof(f51,plain,
    ( v1_finset_1(sK2(sK0))
    | v1_finset_1(k3_tarski(sK0)) ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f50,plain,
    ( v1_finset_1(sK2(sK0))
    | v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,
    ( v1_finset_1(sK2(sK0))
    | v1_finset_1(k3_tarski(sK0))
    | v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(resolution,[],[f25,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_finset_1(k3_tarski(X0))
      | r2_hidden(sK2(X0),X0)
      | ~ v1_finset_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | v1_finset_1(X2)
      | v1_finset_1(k3_tarski(sK0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,
    ( ~ v1_finset_1(sK1)
    | ~ v1_finset_1(k3_tarski(sK0))
    | ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:31:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (8766)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (8768)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.50  % (8768)Refutation not found, incomplete strategy% (8768)------------------------------
% 0.21/0.50  % (8768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8768)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8768)Memory used [KB]: 767
% 0.21/0.50  % (8768)Time elapsed: 0.006 s
% 0.21/0.50  % (8768)------------------------------
% 0.21/0.50  % (8768)------------------------------
% 0.21/0.50  % (8764)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.21/0.51  % (8755)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.51  % (8764)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f27,f59,f94,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v1_finset_1(sK1)),
% 0.21/0.51    inference(resolution,[],[f103,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_finset_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f69,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k3_tarski(sK0)) | v1_finset_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f68,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k3_tarski(sK0))) | v1_finset_1(X0)) )),
% 0.21/0.51    inference(global_subsumption,[],[f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (v1_finset_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k3_tarski(sK0)))) )),
% 0.21/0.51    inference(resolution,[],[f59,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_finset_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_finset_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_finset_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : (v1_finset_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_finset_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_finset_1)).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    r2_hidden(sK1,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f59])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    r2_hidden(sK1,sK0) | ~v1_finset_1(k3_tarski(sK0))),
% 0.21/0.51    inference(resolution,[],[f94,f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ~v1_finset_1(sK0) | r2_hidden(sK1,sK0) | ~v1_finset_1(k3_tarski(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    (~v1_finset_1(k3_tarski(sK0)) | (~v1_finset_1(sK1) & r2_hidden(sK1,sK0)) | ~v1_finset_1(sK0)) & (v1_finset_1(k3_tarski(sK0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0)) & v1_finset_1(sK0)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f19,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0)))) => ((~v1_finset_1(k3_tarski(sK0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,sK0)) | ~v1_finset_1(sK0)) & (v1_finset_1(k3_tarski(sK0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,sK0)) & v1_finset_1(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,sK0)) => (~v1_finset_1(sK1) & r2_hidden(sK1,sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X2] : (v1_finset_1(X2) | ~r2_hidden(X2,X0)) & v1_finset_1(X0))))),
% 0.21/0.51    inference(rectify,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)) & (v1_finset_1(k3_tarski(X0)) | (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0))))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0] : ((~v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))) & (v1_finset_1(k3_tarski(X0)) | (! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0))))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0] : ((! [X1] : (v1_finset_1(X1) | ~r2_hidden(X1,X0)) & v1_finset_1(X0)) <~> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f7])).
% 0.21/0.51  fof(f7,conjecture,(
% 0.21/0.51    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) <=> v1_finset_1(k3_tarski(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_finset_1)).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    v1_finset_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f93,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(k3_tarski(sK0))) | v1_finset_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f72,f35])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(k3_tarski(sK0)))) | v1_finset_1(X0)) )),
% 0.21/0.51    inference(resolution,[],[f67,f30])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    v1_finset_1(k1_zfmisc_1(k3_tarski(sK0)))),
% 0.21/0.51    inference(resolution,[],[f59,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0] : (v1_finset_1(k1_zfmisc_1(X0)) | ~v1_finset_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (v1_finset_1(X0) => v1_finset_1(k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_finset_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    v1_finset_1(k3_tarski(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f58,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    v1_finset_1(k3_tarski(sK0)) | v1_finset_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_finset_1(k3_tarski(sK0)) | v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f51,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (v1_finset_1(k3_tarski(X0)) | ~v1_finset_1(sK2(X0)) | ~v1_finset_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (~v1_finset_1(sK2(X0)) & r2_hidden(sK2(X0),X0)) | ~v1_finset_1(X0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) => (~v1_finset_1(sK2(X0)) & r2_hidden(sK2(X0),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (v1_finset_1(k3_tarski(X0)) | ? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0] : (v1_finset_1(k3_tarski(X0)) | (? [X1] : (~v1_finset_1(X1) & r2_hidden(X1,X0)) | ~v1_finset_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((! [X1] : (r2_hidden(X1,X0) => v1_finset_1(X1)) & v1_finset_1(X0)) => v1_finset_1(k3_tarski(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l22_finset_1)).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v1_finset_1(sK2(sK0)) | v1_finset_1(k3_tarski(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f50,f24])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v1_finset_1(sK2(sK0)) | v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v1_finset_1(sK2(sK0)) | v1_finset_1(k3_tarski(sK0)) | v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0)),
% 0.21/0.51    inference(resolution,[],[f25,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (v1_finset_1(k3_tarski(X0)) | r2_hidden(sK2(X0),X0) | ~v1_finset_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,sK0) | v1_finset_1(X2) | v1_finset_1(k3_tarski(sK0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ~v1_finset_1(sK1) | ~v1_finset_1(k3_tarski(sK0)) | ~v1_finset_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8764)------------------------------
% 0.21/0.51  % (8764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8764)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8764)Memory used [KB]: 5373
% 0.21/0.51  % (8764)Time elapsed: 0.008 s
% 0.21/0.51  % (8764)------------------------------
% 0.21/0.51  % (8764)------------------------------
% 0.21/0.51  % (8762)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (8752)Success in time 0.155 s
%------------------------------------------------------------------------------
