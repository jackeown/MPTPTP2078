%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   32 ( 139 expanded)
%              Number of leaves         :    6 (  40 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 699 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(global_subsumption,[],[f16,f31,f33])).

fof(f33,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f32,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( ~ v1_finset_1(sK1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & ( v1_finset_1(sK1)
      | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_finset_1(X1)
              | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & ( v1_finset_1(X1)
              | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ( ~ v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
        & ( v1_finset_1(X1)
          | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ v1_finset_1(sK1)
        | ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
      & ( v1_finset_1(sK1)
        | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_finset_1(X1)
            | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & ( v1_finset_1(X1)
            | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <~> v1_finset_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
            <=> v1_finset_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          <=> v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tops_2)).

fof(f32,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1))
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_finset_1(X1)
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))
           => v1_finset_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_tops_2)).

fof(f30,plain,(
    ~ v1_finset_1(sK1) ),
    inference(global_subsumption,[],[f17,f16,f29])).

fof(f29,plain,
    ( ~ v1_finset_1(sK1)
    | ~ l1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(duplicate_literal_removal,[],[f28])).

fof(f28,plain,
    ( ~ v1_finset_1(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_finset_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f27,f23])).

fof(f23,plain,(
    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f21,f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f27,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)))
    | ~ l1_struct_0(sK0)
    | ~ v1_finset_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f26,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f26,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_finset_1(k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(sK0),sK1)))
      | ~ l1_struct_0(X0)
      | ~ v1_finset_1(sK1) ) ),
    inference(resolution,[],[f20,f19])).

fof(f19,plain,
    ( ~ v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))
    | ~ v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,
    ( v1_finset_1(sK1)
    | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f16,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:38:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (14359)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.42  % (14360)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (14359)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(global_subsumption,[],[f16,f31,f33])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.42    inference(resolution,[],[f32,f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ((~v1_finset_1(sK1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))) & (v1_finset_1(sK1) | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f14,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((~v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))) & (v1_finset_1(X1) | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0)) => (? [X1] : ((~v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1))) & (v1_finset_1(X1) | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_struct_0(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ? [X1] : ((~v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1))) & (v1_finset_1(X1) | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~v1_finset_1(sK1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))) & (v1_finset_1(sK1) | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((~v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))) & (v1_finset_1(X1) | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (((~v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))) & (v1_finset_1(X1) | v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.42    inference(nnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : ((v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) <~> v1_finset_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) <=> v1_finset_1(X1))))),
% 0.21/0.42    inference(negated_conjecture,[],[f4])).
% 0.21/0.42  fof(f4,conjecture,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) <=> v1_finset_1(X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tops_2)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),sK1)) | ~l1_struct_0(X0)) )),
% 0.21/0.42    inference(resolution,[],[f30,f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((v1_finset_1(X1) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_finset_1(k7_setfam_1(u1_struct_0(X0),X1)) => v1_finset_1(X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_tops_2)).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ~v1_finset_1(sK1)),
% 0.21/0.42    inference(global_subsumption,[],[f17,f16,f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ~v1_finset_1(sK1) | ~l1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~v1_finset_1(sK1) | ~l1_struct_0(sK0) | ~v1_finset_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.42    inference(forward_demodulation,[],[f27,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.42    inference(resolution,[],[f21,f17])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))) | ~l1_struct_0(sK0) | ~v1_finset_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.42    inference(resolution,[],[f26,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0] : (~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_finset_1(k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(sK0),sK1))) | ~l1_struct_0(X0) | ~v1_finset_1(sK1)) )),
% 0.21/0.42    inference(resolution,[],[f20,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ~v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1)) | ~v1_finset_1(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.42    inference(resolution,[],[f30,f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    v1_finset_1(sK1) | v1_finset_1(k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    l1_struct_0(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f15])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (14359)------------------------------
% 0.21/0.42  % (14359)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (14359)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (14359)Memory used [KB]: 6140
% 0.21/0.42  % (14359)Time elapsed: 0.005 s
% 0.21/0.42  % (14359)------------------------------
% 0.21/0.42  % (14359)------------------------------
% 0.21/0.42  % (14354)Success in time 0.064 s
%------------------------------------------------------------------------------
