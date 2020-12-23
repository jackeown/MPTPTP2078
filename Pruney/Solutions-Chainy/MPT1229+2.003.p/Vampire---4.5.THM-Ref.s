%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  83 expanded)
%              Number of leaves         :    6 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 587 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(global_subsumption,[],[f19,f18,f17,f16,f15,f14,f26])).

fof(f26,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ~ v3_pre_topc(k3_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f20,f24])).

fof(f24,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2) ),
    inference(resolution,[],[f21,f17])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f20,plain,(
    ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).

fof(f10,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] :
        ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v3_pre_topc(X1,X0) )
                 => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v3_pre_topc(X1,X0) )
               => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f14,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:57:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (5045)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.42  % (5044)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (5042)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.43  % (5046)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.43  % (5042)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(global_subsumption,[],[f19,f18,f17,f16,f15,f14,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.43    inference(resolution,[],[f22,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ~v3_pre_topc(k3_xboole_0(sK1,sK2),sK0)),
% 0.21/0.43    inference(superposition,[],[f20,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) )),
% 0.21/0.43    inference(resolution,[],[f21,f17])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ((~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f12,f11,f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v3_pre_topc(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : (~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f5])).
% 0.21/0.43  fof(f5,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (? [X2] : ((~v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.43    inference(negated_conjecture,[],[f3])).
% 0.21/0.43  fof(f3,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v3_pre_topc(X1,X0)) => v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_1)).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 0.21/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    v2_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    v3_pre_topc(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    v3_pre_topc(sK2,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (5042)------------------------------
% 0.21/0.43  % (5042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (5042)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (5042)Memory used [KB]: 6140
% 0.21/0.43  % (5042)Time elapsed: 0.032 s
% 0.21/0.43  % (5042)------------------------------
% 0.21/0.43  % (5042)------------------------------
% 0.21/0.44  % (5029)Success in time 0.079 s
%------------------------------------------------------------------------------
