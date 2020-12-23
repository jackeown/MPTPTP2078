%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   20 (  44 expanded)
%              Number of leaves         :    5 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 223 expanded)
%              Number of equality atoms :   37 ( 103 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f16])).

fof(f16,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f11])).

% (30661)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f11,plain,
    ( sK1 != sK2
    & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f10,f9,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(sK0),X1) = k3_subset_1(u1_struct_0(sK0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (30660)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f9,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & k3_subset_1(u1_struct_0(sK0),X1) = k3_subset_1(u1_struct_0(sK0),X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & k3_subset_1(u1_struct_0(sK0),X2) = k3_subset_1(u1_struct_0(sK0),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] :
        ( sK1 != X2
        & k3_subset_1(u1_struct_0(sK0),X2) = k3_subset_1(u1_struct_0(sK0),sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( sK1 != sK2
      & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).

fof(f23,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f22,f15])).

fof(f15,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f18,f14])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f18,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),X0)
      | sK1 = X0 ) ),
    inference(resolution,[],[f17,f13])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( k3_subset_1(X0,X1) = k3_subset_1(X0,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:53:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (30651)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (30666)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (30669)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (30671)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (30673)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (30664)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (30672)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (30672)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f23,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    sK1 != sK2),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  % (30661)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ((sK1 != sK2 & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f10,f9,f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (X1 != X2 & k3_subset_1(u1_struct_0(sK0),X1) = k3_subset_1(u1_struct_0(sK0),X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  % (30660)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (X1 != X2 & k3_subset_1(u1_struct_0(sK0),X1) = k3_subset_1(u1_struct_0(sK0),X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (sK1 != X2 & k3_subset_1(u1_struct_0(sK0),X2) = k3_subset_1(u1_struct_0(sK0),sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X2] : (sK1 != X2 & k3_subset_1(u1_struct_0(sK0),X2) = k3_subset_1(u1_struct_0(sK0),sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (sK1 != sK2 & k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f5,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f4])).
% 0.21/0.52  fof(f4,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) => X1 = X2))))),
% 0.21/0.52    inference(negated_conjecture,[],[f2])).
% 0.21/0.52  fof(f2,conjecture,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k3_subset_1(u1_struct_0(X0),X1) = k3_subset_1(u1_struct_0(X0),X2) => X1 = X2))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tops_1)).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    sK1 = sK2),
% 0.21/0.52    inference(subsumption_resolution,[],[f22,f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK1) = k3_subset_1(u1_struct_0(sK0),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),sK2) | sK1 = sK2),
% 0.21/0.52    inference(resolution,[],[f18,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),sK1) != k3_subset_1(u1_struct_0(sK0),X0) | sK1 = X0) )),
% 0.21/0.52    inference(resolution,[],[f17,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) != k3_subset_1(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | k3_subset_1(X0,X1) != k3_subset_1(X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f6])).
% 0.21/0.52  fof(f6,plain,(
% 0.21/0.52    ! [X0,X1] : (! [X2] : ((X1 = X2 | k3_subset_1(X0,X1) != k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (k3_subset_1(X0,X1) = k3_subset_1(X0,X2) => X1 = X2)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_subset_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (30672)------------------------------
% 0.21/0.52  % (30672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30672)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (30672)Memory used [KB]: 6140
% 0.21/0.52  % (30672)Time elapsed: 0.105 s
% 0.21/0.52  % (30672)------------------------------
% 0.21/0.52  % (30672)------------------------------
% 0.21/0.52  % (30662)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (30663)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (30654)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (30657)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (30656)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (30645)Success in time 0.162 s
%------------------------------------------------------------------------------
