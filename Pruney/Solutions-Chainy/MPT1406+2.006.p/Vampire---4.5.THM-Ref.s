%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 137 expanded)
%              Number of leaves         :   18 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  210 ( 488 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (8588)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
fof(f149,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f58,f73,f93,f98,f122,f148])).

fof(f148,plain,
    ( ~ spl3_10
    | spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f146,f118,f35,f90])).

fof(f90,plain,
    ( spl3_10
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f35,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f118,plain,
    ( spl3_13
  <=> k1_tops_1(sK0,sK2) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f146,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | spl3_1
    | ~ spl3_13 ),
    inference(superposition,[],[f59,f120])).

fof(f120,plain,
    ( k1_tops_1(sK0,sK2) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f59,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK1,X0),sK2)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f37,f28])).

fof(f28,plain,(
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

fof(f37,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f122,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f116,f95,f118])).

fof(f95,plain,
    ( spl3_11
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( k1_tops_1(sK0,sK2) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_11 ),
    inference(resolution,[],[f97,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f97,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f98,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f87,f70,f55,f50,f45,f40,f95])).

fof(f40,plain,
    ( spl3_2
  <=> m2_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f45,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f55,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f70,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f87,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f57,f52,f42,f47,f72,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f72,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f47,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f42,plain,
    ( m2_connsp_2(sK2,sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f52,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f93,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f88,f70,f50,f90])).

fof(f88,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f52,f72,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f73,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f68,f55,f50,f45,f40,f70])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f57,f52,f42,f47,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f58,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r1_tarski(sK1,sK2)
    & m2_connsp_2(sK2,sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,X2)
                & m2_connsp_2(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,sK0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & m2_connsp_2(X2,sK0,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & m2_connsp_2(X2,sK0,sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,X2)
        & m2_connsp_2(X2,sK0,sK1) )
   => ( ~ r1_tarski(sK1,sK2)
      & m2_connsp_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_connsp_2(X2,X0,X1)
               => r1_tarski(X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_connsp_2(X2,X0,X1)
               => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_connsp_2(X2,X0,X1)
             => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_connsp_2)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f40])).

fof(f26,plain,(
    m2_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f35])).

fof(f27,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (8575)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (8571)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (8583)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (8593)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (8576)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (8572)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (8585)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (8581)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (8589)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.52  % (8570)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (8590)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (8580)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (8579)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (8574)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.52  % (8578)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (8576)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  % (8588)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f38,f43,f48,f53,f58,f73,f93,f98,f122,f148])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ~spl3_10 | spl3_1 | ~spl3_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f146,f118,f35,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    spl3_10 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl3_13 <=> k1_tops_1(sK0,sK2) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (spl3_1 | ~spl3_13)),
% 0.22/0.52    inference(superposition,[],[f59,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    k1_tops_1(sK0,sK2) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) | ~spl3_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK1,X0),sK2)) ) | spl3_1),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f37,f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK2) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f35])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    spl3_13 | ~spl3_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f116,f95,f118])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    spl3_11 <=> r1_tarski(sK1,k1_tops_1(sK0,sK2))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    k1_tops_1(sK0,sK2) = k2_xboole_0(sK1,k1_tops_1(sK0,sK2)) | ~spl3_11),
% 0.22/0.52    inference(resolution,[],[f97,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_tops_1(sK0,sK2)) | ~spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f95])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl3_11 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f87,f70,f55,f50,f45,f40,f95])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    spl3_2 <=> m2_connsp_2(sK2,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    spl3_4 <=> l1_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl3_5 <=> v2_pre_topc(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    r1_tarski(sK1,k1_tops_1(sK0,sK2)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f57,f52,f42,f47,f72,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f45])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    m2_connsp_2(sK2,sK0,sK1) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f40])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    l1_pre_topc(sK0) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f50])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    v2_pre_topc(sK0) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    spl3_10 | ~spl3_4 | ~spl3_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f88,f70,f50,f90])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl3_4 | ~spl3_7)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f52,f72,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    spl3_7 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f68,f55,f50,f45,f40,f70])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5)),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f57,f52,f42,f47,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ((~r1_tarski(sK1,sK2) & m2_connsp_2(sK2,sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19,f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(sK1,X2) & m2_connsp_2(X2,sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X2] : (~r1_tarski(sK1,X2) & m2_connsp_2(X2,sK0,sK1)) => (~r1_tarski(sK1,sK2) & m2_connsp_2(sK2,sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m2_connsp_2(X2,X0,X1) => r1_tarski(X1,X2))))),
% 0.22/0.52    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.52  fof(f7,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m2_connsp_2(X2,X0,X1) => r1_tarski(X1,X2))))),
% 0.22/0.52    inference(negated_conjecture,[],[f6])).
% 0.22/0.52  fof(f6,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m2_connsp_2(X2,X0,X1) => r1_tarski(X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_connsp_2)).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f50])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f45])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f40])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    m2_connsp_2(sK2,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f35])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (8576)------------------------------
% 0.22/0.52  % (8576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8576)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (8576)Memory used [KB]: 10746
% 0.22/0.52  % (8576)Time elapsed: 0.092 s
% 0.22/0.52  % (8576)------------------------------
% 0.22/0.52  % (8576)------------------------------
% 0.22/0.52  % (8578)Refutation not found, incomplete strategy% (8578)------------------------------
% 0.22/0.52  % (8578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8578)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8578)Memory used [KB]: 10490
% 0.22/0.52  % (8578)Time elapsed: 0.104 s
% 0.22/0.52  % (8578)------------------------------
% 0.22/0.52  % (8578)------------------------------
% 0.22/0.52  % (8569)Success in time 0.158 s
%------------------------------------------------------------------------------
