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
% DateTime   : Thu Dec  3 13:16:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  145 ( 472 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f79,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f37,f70,f78])).

fof(f78,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f34,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f74,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f74,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f16,f17,f31,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f31,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_1
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
      | ~ v1_tops_2(sK1,sK0) )
    & ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | ~ v1_tops_2(X1,X0) )
            & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
            | ~ v1_tops_2(X1,sK0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
          | ~ v1_tops_2(X1,sK0) )
        & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
          | v1_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
        | ~ v1_tops_2(sK1,sK0) )
      & ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
        | v1_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | ~ v1_tops_2(X1,X0) )
          & ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f69])).

fof(f69,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f68,f16])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f67,f30])).

fof(f30,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f67,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f55,f39])).

fof(f39,plain,
    ( r1_tarski(sK1,u1_pre_topc(sK0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f35,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f55,plain,
    ( ~ r1_tarski(sK1,u1_pre_topc(sK0))
    | v1_tops_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f23,f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f27,f33,f29])).

fof(f27,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f19,f20])).

fof(f20,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f19,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f26,f33,f29])).

fof(f26,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))
    | v1_tops_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f18,f20])).

fof(f18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0)))))
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:37:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (15182)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (15179)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (15179)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f36,f37,f70,f78])).
% 0.21/0.43  fof(f78,plain,(
% 0.21/0.43    ~spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    $false | (~spl2_1 | spl2_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f76,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) | spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0)))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.43  fof(f76,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) | ~spl2_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f74,f25])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.43    inference(nnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.43  fof(f74,plain,(
% 0.21/0.43    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl2_1),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f16,f17,f31,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    v1_tops_2(sK1,sK0) | ~spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    spl2_1 <=> v1_tops_2(sK1,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~v1_tops_2(sK1,sK0)) & (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f12,f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~v1_tops_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~v1_tops_2(X1,sK0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~v1_tops_2(X1,sK0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~v1_tops_2(sK1,sK0)) & (m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~v1_tops_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(flattening,[],[f9])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : (((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | ~v1_tops_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(nnf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,plain,(
% 0.21/0.43    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,plain,(
% 0.21/0.43    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))))))),
% 0.21/0.43    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.43  fof(f5,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))))))),
% 0.21/0.43    inference(negated_conjecture,[],[f4])).
% 0.21/0.43  fof(f4,conjecture,(
% 0.21/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))))))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_1)).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    l1_pre_topc(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    spl2_1 | ~spl2_2),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f68,f16])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_2)),
% 0.21/0.43    inference(subsumption_resolution,[],[f67,f30])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ~v1_tops_2(sK1,sK0) | spl2_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f29])).
% 0.21/0.43  fof(f67,plain,(
% 0.21/0.43    v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.21/0.43    inference(subsumption_resolution,[],[f55,f39])).
% 0.21/0.43  fof(f39,plain,(
% 0.21/0.43    r1_tarski(sK1,u1_pre_topc(sK0)) | ~spl2_2),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f35,f24])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) | ~spl2_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f33])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    ~r1_tarski(sK1,u1_pre_topc(sK0)) | v1_tops_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.43    inference(resolution,[],[f23,f17])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f37,plain,(
% 0.21/0.43    ~spl2_1 | ~spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f27,f33,f29])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) | ~v1_tops_2(sK1,sK0)),
% 0.21/0.43    inference(backward_demodulation,[],[f19,f20])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | ~v1_tops_2(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    spl2_1 | spl2_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f26,f33,f29])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_pre_topc(sK0))) | v1_tops_2(sK1,sK0)),
% 0.21/0.43    inference(backward_demodulation,[],[f18,f20])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k2_yellow_1(u1_pre_topc(sK0))))) | v1_tops_2(sK1,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (15179)------------------------------
% 0.21/0.43  % (15179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (15179)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (15179)Memory used [KB]: 6140
% 0.21/0.43  % (15179)Time elapsed: 0.005 s
% 0.21/0.43  % (15179)------------------------------
% 0.21/0.43  % (15179)------------------------------
% 0.21/0.43  % (15176)Success in time 0.076 s
%------------------------------------------------------------------------------
