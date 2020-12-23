%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 123 expanded)
%              Number of leaves         :    8 (  38 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 554 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f33,f62,f74])).

fof(f74,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f72,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v1_tops_2(sK1,sK0) )
    & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
      | v1_tops_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v1_tops_2(X1,X0) )
            & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | v1_tops_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | ~ v1_tops_2(X1,sK0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
            | v1_tops_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | ~ v1_tops_2(X1,sK0) )
        & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0)
          | v1_tops_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | ~ v1_tops_2(sK1,sK0) )
      & ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
        | v1_tops_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | ~ v1_tops_2(X1,X0) )
          & ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
            | v1_tops_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tops_2(X1,X0)
          <~> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v1_tops_2(X1,X0)
            <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f36,plain,(
    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f17,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f17,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f30,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl2_2
  <=> v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f70,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f66,f27])).

fof(f27,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f66,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f21,f34])).

fof(f34,plain,(
    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f17,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).

fof(f62,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f61])).

fof(f61,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f60,f26])).

fof(f26,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f60,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f59,f34])).

fof(f59,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f58,f16])).

fof(f58,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f52,f31])).

fof(f31,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f52,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f20,f36])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_tops_2(X1,X0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f19,f29,f25])).

fof(f19,plain,
    ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f18,f29,f25])).

fof(f18,plain,
    ( v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.42  % (20278)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.42  % (20278)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f32,f33,f62,f74])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    ~spl2_1 | spl2_2),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f73])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    $false | (~spl2_1 | spl2_2)),
% 0.22/0.42    inference(subsumption_resolution,[],[f72,f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    l1_pre_topc(sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tops_2(sK1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | ~v1_tops_2(X1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | ~v1_tops_2(X1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),X1),sK0) | v1_tops_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => ((~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tops_2(sK1,sK0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : ((~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v1_tops_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.42    inference(flattening,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : (((~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v1_tops_2(X1,X0)) & (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v1_tops_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.42    inference(nnf_transformation,[],[f6])).
% 0.22/0.42  fof(f6,plain,(
% 0.22/0.42    ? [X0] : (? [X1] : ((v1_tops_2(X1,X0) <~> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,negated_conjecture,(
% 0.22/0.42    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.42    inference(negated_conjecture,[],[f4])).
% 0.22/0.42  fof(f4,conjecture,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tops_2)).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    ~l1_pre_topc(sK0) | (~spl2_1 | spl2_2)),
% 0.22/0.42    inference(subsumption_resolution,[],[f71,f36])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f17,f23])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.42    inference(cnf_transformation,[],[f9])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.42    inference(ennf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f71,plain,(
% 0.22/0.42    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | (~spl2_1 | spl2_2)),
% 0.22/0.42    inference(subsumption_resolution,[],[f70,f30])).
% 0.22/0.42  fof(f30,plain,(
% 0.22/0.42    ~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f29])).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    spl2_2 <=> v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.42    inference(subsumption_resolution,[],[f66,f27])).
% 0.22/0.42  fof(f27,plain,(
% 0.22/0.42    v1_tops_2(sK1,sK0) | ~spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f25,plain,(
% 0.22/0.42    spl2_1 <=> v1_tops_2(sK1,sK0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.42  fof(f66,plain,(
% 0.22/0.42    ~v1_tops_2(sK1,sK0) | v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)),
% 0.22/0.42    inference(superposition,[],[f21,f34])).
% 0.22/0.42  fof(f34,plain,(
% 0.22/0.42    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.22/0.42    inference(unit_resulting_resolution,[],[f17,f22])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.22/0.42    inference(cnf_transformation,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | v2_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : (((v2_tops_2(X1,X0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) & (v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~v2_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.42    inference(nnf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,plain,(
% 0.22/0.42    ! [X0] : (! [X1] : ((v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tops_2)).
% 0.22/0.42  fof(f62,plain,(
% 0.22/0.42    spl2_1 | ~spl2_2),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f61])).
% 0.22/0.42  fof(f61,plain,(
% 0.22/0.42    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.42    inference(subsumption_resolution,[],[f60,f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    ~v1_tops_2(sK1,sK0) | spl2_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f25])).
% 0.22/0.42  fof(f60,plain,(
% 0.22/0.42    v1_tops_2(sK1,sK0) | ~spl2_2),
% 0.22/0.42    inference(forward_demodulation,[],[f59,f34])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) | ~spl2_2),
% 0.22/0.42    inference(subsumption_resolution,[],[f58,f16])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.22/0.42    inference(subsumption_resolution,[],[f52,f31])).
% 0.22/0.42  fof(f31,plain,(
% 0.22/0.42    v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_2),
% 0.22/0.42    inference(avatar_component_clause,[],[f29])).
% 0.22/0.42  fof(f52,plain,(
% 0.22/0.42    ~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)),sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.42    inference(resolution,[],[f20,f36])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_2(X1,X0) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f15])).
% 0.22/0.42  fof(f33,plain,(
% 0.22/0.42    ~spl2_1 | ~spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f29,f25])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ~v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tops_2(sK1,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f32,plain,(
% 0.22/0.42    spl2_1 | spl2_2),
% 0.22/0.42    inference(avatar_split_clause,[],[f18,f29,f25])).
% 0.22/0.42  fof(f18,plain,(
% 0.22/0.42    v2_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | v1_tops_2(sK1,sK0)),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (20278)------------------------------
% 0.22/0.42  % (20278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (20278)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (20278)Memory used [KB]: 6140
% 0.22/0.42  % (20278)Time elapsed: 0.005 s
% 0.22/0.42  % (20278)------------------------------
% 0.22/0.42  % (20278)------------------------------
% 0.22/0.43  % (20275)Success in time 0.068 s
%------------------------------------------------------------------------------
