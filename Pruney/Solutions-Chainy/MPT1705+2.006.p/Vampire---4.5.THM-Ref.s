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
% DateTime   : Thu Dec  3 13:17:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 823 expanded)
%              Number of leaves         :   22 ( 256 expanded)
%              Depth                    :   21
%              Number of atoms          :  723 (8983 expanded)
%              Number of equality atoms :   43 ( 708 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1212)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% (1200)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (1218)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (1211)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (1200)Refutation not found, incomplete strategy% (1200)------------------------------
% (1200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1200)Termination reason: Refutation not found, incomplete strategy

% (1200)Memory used [KB]: 10618
% (1200)Time elapsed: 0.112 s
% (1200)------------------------------
% (1200)------------------------------
% (1208)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (1211)Refutation not found, incomplete strategy% (1211)------------------------------
% (1211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1211)Termination reason: Refutation not found, incomplete strategy

% (1211)Memory used [KB]: 10618
% (1211)Time elapsed: 0.115 s
% (1211)------------------------------
% (1211)------------------------------
% (1202)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (1214)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f612,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f102,f105,f191,f386,f390,f457,f479,f611])).

fof(f611,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f609,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( ~ m1_pre_topc(sK2,sK0)
      | ~ v1_tsep_1(sK2,sK0)
      | ~ m1_pre_topc(sK1,sK0)
      | ~ v1_tsep_1(sK1,sK0) )
    & ( ( m1_pre_topc(sK2,sK0)
        & v1_tsep_1(sK2,sK0) )
      | ( m1_pre_topc(sK1,sK0)
        & v1_tsep_1(sK1,sK0) ) )
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) ) )
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                & l1_pre_topc(X2)
                & v2_pre_topc(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,sK0)
                | ~ v1_tsep_1(X2,sK0)
                | ~ m1_pre_topc(X1,sK0)
                | ~ v1_tsep_1(X1,sK0) )
              & ( ( m1_pre_topc(X2,sK0)
                  & v1_tsep_1(X2,sK0) )
                | ( m1_pre_topc(X1,sK0)
                  & v1_tsep_1(X1,sK0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_pre_topc(X2,sK0)
              | ~ v1_tsep_1(X2,sK0)
              | ~ m1_pre_topc(X1,sK0)
              | ~ v1_tsep_1(X1,sK0) )
            & ( ( m1_pre_topc(X2,sK0)
                & v1_tsep_1(X2,sK0) )
              | ( m1_pre_topc(X1,sK0)
                & v1_tsep_1(X1,sK0) ) )
            & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
            & l1_pre_topc(X2)
            & v2_pre_topc(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ( ~ m1_pre_topc(X2,sK0)
            | ~ v1_tsep_1(X2,sK0)
            | ~ m1_pre_topc(sK1,sK0)
            | ~ v1_tsep_1(sK1,sK0) )
          & ( ( m1_pre_topc(X2,sK0)
              & v1_tsep_1(X2,sK0) )
            | ( m1_pre_topc(sK1,sK0)
              & v1_tsep_1(sK1,sK0) ) )
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
          & l1_pre_topc(X2)
          & v2_pre_topc(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2] :
        ( ( ~ m1_pre_topc(X2,sK0)
          | ~ v1_tsep_1(X2,sK0)
          | ~ m1_pre_topc(sK1,sK0)
          | ~ v1_tsep_1(sK1,sK0) )
        & ( ( m1_pre_topc(X2,sK0)
            & v1_tsep_1(X2,sK0) )
          | ( m1_pre_topc(sK1,sK0)
            & v1_tsep_1(sK1,sK0) ) )
        & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2
        & l1_pre_topc(X2)
        & v2_pre_topc(X2) )
   => ( ( ~ m1_pre_topc(sK2,sK0)
        | ~ v1_tsep_1(sK2,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ v1_tsep_1(sK1,sK0) )
      & ( ( m1_pre_topc(sK2,sK0)
          & v1_tsep_1(sK2,sK0) )
        | ( m1_pre_topc(sK1,sK0)
          & v1_tsep_1(sK1,sK0) ) )
      & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_pre_topc(X2,X0)
                | ~ v1_tsep_1(X2,X0)
                | ~ m1_pre_topc(X1,X0)
                | ~ v1_tsep_1(X1,X0) )
              & ( ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) )
                | ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <~> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
              & l1_pre_topc(X2)
              & v2_pre_topc(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2) )
               => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
                 => ( ( m1_pre_topc(X1,X0)
                      & v1_tsep_1(X1,X0) )
                  <=> ( m1_pre_topc(X2,X0)
                      & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f609,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f608,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f608,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f607,f477])).

fof(f477,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f476,f50])).

fof(f50,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f476,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f474,f45])).

fof(f474,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f91,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

% (1201)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f90,plain,
    ( spl3_2
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f607,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f606,f96])).

fof(f96,plain,
    ( ~ v1_tsep_1(sK2,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_3
  <=> v1_tsep_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f606,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(resolution,[],[f503,f471])).

fof(f471,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f470,f131])).

fof(f131,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f110,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f110,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f59,f47])).

fof(f47,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f470,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f469,f44])).

fof(f469,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f468,f45])).

fof(f468,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f467,f91])).

fof(f467,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f84,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_tsep_1(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ v3_pre_topc(X2,X0) )
                & ( v3_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f87,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_1
  <=> v1_tsep_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f503,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(k2_struct_0(sK1),X0)
        | v1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl3_19 ),
    inference(superposition,[],[f306,f385])).

fof(f385,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f306,plain,(
    ! [X7] :
      ( ~ v3_pre_topc(k2_struct_0(sK2),X7)
      | v1_tsep_1(sK2,X7)
      | ~ m1_pre_topc(sK2,X7)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7) ) ),
    inference(superposition,[],[f107,f148])).

fof(f148,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f111,f58])).

fof(f111,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f59,f49])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(u1_struct_0(X1),X0)
      | v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f80,f60])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ v3_pre_topc(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f479,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f477,f100])).

fof(f100,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f457,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f455,f44])).

fof(f455,plain,
    ( ~ v2_pre_topc(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f454,f45])).

fof(f454,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f453,f192])).

fof(f192,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f188,f45])).

fof(f188,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f147,f99])).

fof(f99,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f146,f48])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f145,f49])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f144,f46])).

fof(f46,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f143,f47])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | m1_pre_topc(sK1,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f78,f50])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  | ~ m1_pre_topc(X2,X0) )
                & ( m1_pre_topc(X2,X0)
                  | ~ m1_pre_topc(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X0)
              <=> m1_pre_topc(X2,X0) )
              | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1
               => ( m1_pre_topc(X1,X0)
                <=> m1_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(f453,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f452,f88])).

fof(f88,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f452,plain,
    ( v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(resolution,[],[f248,f400])).

fof(f400,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(superposition,[],[f300,f385])).

fof(f300,plain,
    ( v3_pre_topc(k2_struct_0(sK2),sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f130,f148])).

fof(f130,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f129,f44])).

fof(f129,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f127,f99])).

fof(f127,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v3_pre_topc(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f108,f95])).

fof(f95,plain,
    ( v1_tsep_1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f248,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k2_struct_0(sK1),X5)
      | v1_tsep_1(sK1,X5)
      | ~ m1_pre_topc(sK1,X5)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5) ) ),
    inference(superposition,[],[f107,f131])).

fof(f390,plain,(
    spl3_18 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | spl3_18 ),
    inference(subsumption_resolution,[],[f388,f381])).

fof(f381,plain,
    ( ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl3_18
  <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f388,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f281,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f281,plain,(
    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f280,f148])).

fof(f280,plain,(
    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f279,f242])).

fof(f242,plain,(
    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[],[f50,f131])).

fof(f279,plain,(
    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) ),
    inference(subsumption_resolution,[],[f278,f46])).

fof(f278,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f277,f47])).

fof(f277,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f250,f118])).

fof(f118,plain,(
    v4_pre_topc(k2_struct_0(sK1),sK1) ),
    inference(subsumption_resolution,[],[f115,f47])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK1)
    | v4_pre_topc(k2_struct_0(sK1),sK1) ),
    inference(resolution,[],[f64,f46])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f250,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK1),sK1)
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(superposition,[],[f133,f131])).

fof(f133,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),X0)
      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f106])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f57,f56])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f386,plain,
    ( ~ spl3_18
    | spl3_19 ),
    inference(avatar_split_clause,[],[f376,f383,f379])).

fof(f376,plain,
    ( k2_struct_0(sK1) = k2_struct_0(sK2)
    | ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f368,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f368,plain,(
    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) ),
    inference(resolution,[],[f200,f75])).

fof(f200,plain,(
    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f199,f119])).

fof(f119,plain,(
    v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK2)
    | v4_pre_topc(k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f64,f48])).

fof(f199,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK2),sK2)
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f198,f148])).

fof(f198,plain,
    ( m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v4_pre_topc(u1_struct_0(sK2),sK2) ),
    inference(forward_demodulation,[],[f197,f148])).

fof(f197,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v4_pre_topc(u1_struct_0(sK2),sK2) ),
    inference(resolution,[],[f142,f106])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK2) ) ),
    inference(forward_demodulation,[],[f141,f131])).

fof(f141,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f140,f46])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK1) ) ),
    inference(subsumption_resolution,[],[f139,f47])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1) ) ),
    inference(superposition,[],[f71,f50])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f191,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f189,f45])).

fof(f189,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f188,f92])).

fof(f92,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f105,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f51,f94,f86])).

fof(f51,plain,
    ( v1_tsep_1(sK2,sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,
    ( spl3_2
    | spl3_4 ),
    inference(avatar_split_clause,[],[f54,f98,f90])).

fof(f54,plain,
    ( m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f101,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f98,f94,f90,f86])).

fof(f55,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ v1_tsep_1(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v1_tsep_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (1225)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.46  % (1209)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (1203)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (1222)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (1204)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (1210)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (1219)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (1210)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  % (1212)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (1200)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (1218)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (1211)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (1200)Refutation not found, incomplete strategy% (1200)------------------------------
% 0.21/0.51  % (1200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1200)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1200)Memory used [KB]: 10618
% 0.21/0.51  % (1200)Time elapsed: 0.112 s
% 0.21/0.51  % (1200)------------------------------
% 0.21/0.51  % (1200)------------------------------
% 0.21/0.51  % (1208)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (1211)Refutation not found, incomplete strategy% (1211)------------------------------
% 0.21/0.52  % (1211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1211)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1211)Memory used [KB]: 10618
% 0.21/0.52  % (1211)Time elapsed: 0.115 s
% 0.21/0.52  % (1211)------------------------------
% 0.21/0.52  % (1211)------------------------------
% 0.21/0.52  % (1202)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (1214)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  fof(f612,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f101,f102,f105,f191,f386,f390,f457,f479,f611])).
% 0.21/0.52  fof(f611,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_19),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f610])).
% 0.21/0.52  fof(f610,plain,(
% 0.21/0.52    $false | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f609,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    (((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f34,f33,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(X1,sK0) | ~v1_tsep_1(X1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(X1,sK0) & v1_tsep_1(X1,sK0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X2] : ((~m1_pre_topc(X2,sK0) | ~v1_tsep_1(X2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(X2,sK0) & v1_tsep_1(X2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) => ((~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)) & ((m1_pre_topc(sK2,sK0) & v1_tsep_1(sK2,sK0)) | (m1_pre_topc(sK1,sK0) & v1_tsep_1(sK1,sK0))) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2 & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((((~m1_pre_topc(X2,X0) | ~v1_tsep_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)) | (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 & l1_pre_topc(X2) & v2_pre_topc(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0))) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2) & (l1_pre_topc(X2) & v2_pre_topc(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f13])).
% 0.21/0.53  fof(f13,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_tsep_1(X2,X0)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tmap_1)).
% 0.21/0.53  fof(f609,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f608,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f608,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f607,f477])).
% 0.21/0.53  fof(f477,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~spl3_2),
% 0.21/0.53    inference(forward_demodulation,[],[f476,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f476,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~spl3_2),
% 0.21/0.53    inference(subsumption_resolution,[],[f474,f45])).
% 0.21/0.53  fof(f474,plain,(
% 0.21/0.53    m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK0) | ~l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.53    inference(resolution,[],[f91,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  % (1201)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl3_2 <=> m1_pre_topc(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.53  fof(f607,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f606,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ~v1_tsep_1(sK2,sK0) | spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl3_3 <=> v1_tsep_1(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f606,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_1 | ~spl3_2 | ~spl3_19)),
% 0.21/0.53    inference(resolution,[],[f503,f471])).
% 0.21/0.53  fof(f471,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(forward_demodulation,[],[f470,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f110,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f59,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f470,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f469,f44])).
% 0.21/0.53  fof(f469,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f468,f45])).
% 0.21/0.53  fof(f468,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_1 | ~spl3_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f467,f91])).
% 0.21/0.53  fof(f467,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_1),
% 0.21/0.53    inference(resolution,[],[f87,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v3_pre_topc(u1_struct_0(X1),X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    v1_tsep_1(sK1,sK0) | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl3_1 <=> v1_tsep_1(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f503,plain,(
% 0.21/0.53    ( ! [X0] : (~v3_pre_topc(k2_struct_0(sK1),X0) | v1_tsep_1(sK2,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl3_19),
% 0.21/0.53    inference(superposition,[],[f306,f385])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_struct_0(sK2) | ~spl3_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f383])).
% 0.21/0.53  fof(f383,plain,(
% 0.21/0.53    spl3_19 <=> k2_struct_0(sK1) = k2_struct_0(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    ( ! [X7] : (~v3_pre_topc(k2_struct_0(sK2),X7) | v1_tsep_1(sK2,X7) | ~m1_pre_topc(sK2,X7) | ~l1_pre_topc(X7) | ~v2_pre_topc(X7)) )),
% 0.21/0.53    inference(superposition,[],[f107,f148])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f111,f58])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    l1_struct_0(sK2)),
% 0.21/0.53    inference(resolution,[],[f59,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    l1_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_pre_topc(u1_struct_0(X1),X0) | v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f80,f60])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_tsep_1(X1,X0) | ~v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f479,plain,(
% 0.21/0.53    ~spl3_2 | spl3_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f478])).
% 0.21/0.53  fof(f478,plain,(
% 0.21/0.53    $false | (~spl3_2 | spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f477,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK0) | spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f98])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    spl3_4 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_19),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f456])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    $false | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f455,f44])).
% 0.21/0.53  fof(f455,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f454,f45])).
% 0.21/0.53  fof(f454,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f453,f192])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~spl3_4),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f45])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f147,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f98])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    v2_pre_topc(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f49])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    v2_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f143,f47])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_pre_topc(sK2,X0) | m1_pre_topc(sK1,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(superposition,[],[f78,f50])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X2,X0] : (~m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) & (m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0))) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0)) | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != X1) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X1 => (m1_pre_topc(X1,X0) <=> m1_pre_topc(X2,X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).
% 0.21/0.53  fof(f453,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.53    inference(subsumption_resolution,[],[f452,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~v1_tsep_1(sK1,sK0) | spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f452,plain,(
% 0.21/0.53    v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.53    inference(resolution,[],[f248,f400])).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_19)),
% 0.21/0.53    inference(superposition,[],[f300,f385])).
% 0.21/0.53  fof(f300,plain,(
% 0.21/0.53    v3_pre_topc(k2_struct_0(sK2),sK0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(superposition,[],[f130,f148])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f44])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f128,f45])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    v3_pre_topc(u1_struct_0(sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f127,f99])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK0) | v3_pre_topc(u1_struct_0(sK2),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 0.21/0.53    inference(resolution,[],[f108,f95])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK0) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ( ! [X5] : (~v3_pre_topc(k2_struct_0(sK1),X5) | v1_tsep_1(sK1,X5) | ~m1_pre_topc(sK1,X5) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5)) )),
% 0.21/0.53    inference(superposition,[],[f107,f131])).
% 0.21/0.53  fof(f390,plain,(
% 0.21/0.53    spl3_18),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f389])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    $false | spl3_18),
% 0.21/0.53    inference(subsumption_resolution,[],[f388,f381])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) | spl3_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f379])).
% 0.21/0.53  fof(f379,plain,(
% 0.21/0.53    spl3_18 <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.53  fof(f388,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f281,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.53    inference(forward_demodulation,[],[f280,f148])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.53    inference(forward_demodulation,[],[f279,f242])).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    sK2 = g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))),
% 0.21/0.53    inference(superposition,[],[f50,f131])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1)))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f278,f46])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f277,f47])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f250,f118])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    v4_pre_topc(k2_struct_0(sK1),sK1)),
% 0.21/0.53    inference(subsumption_resolution,[],[f115,f47])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | v4_pre_topc(k2_struct_0(sK1),sK1)),
% 0.21/0.53    inference(resolution,[],[f64,f46])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ~v4_pre_topc(k2_struct_0(sK1),sK1) | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK1),u1_pre_topc(sK1))))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 0.21/0.53    inference(superposition,[],[f133,f131])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X0] : (~v4_pre_topc(u1_struct_0(X0),X0) | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f69,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f57,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).
% 0.21/0.53  fof(f386,plain,(
% 0.21/0.53    ~spl3_18 | spl3_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f376,f383,f379])).
% 0.21/0.53  fof(f376,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_struct_0(sK2) | ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.21/0.53    inference(resolution,[],[f368,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1))),
% 0.21/0.53    inference(resolution,[],[f200,f75])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f199,f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    v4_pre_topc(k2_struct_0(sK2),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f116,f49])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ~l1_pre_topc(sK2) | v4_pre_topc(k2_struct_0(sK2),sK2)),
% 0.21/0.53    inference(resolution,[],[f64,f48])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ~v4_pre_topc(k2_struct_0(sK2),sK2) | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.21/0.53    inference(forward_demodulation,[],[f198,f148])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(u1_struct_0(sK2),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f197,f148])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(u1_struct_0(sK2),sK2)),
% 0.21/0.53    inference(resolution,[],[f142,f106])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v4_pre_topc(X0,sK2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f141,f131])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f140,f46])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK2) | ~v2_pre_topc(sK1)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f139,f47])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)) )),
% 0.21/0.53    inference(superposition,[],[f71,f50])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    spl3_2 | ~spl3_4),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    $false | (spl3_2 | ~spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f189,f45])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f188,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ~m1_pre_topc(sK1,sK0) | spl3_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl3_1 | spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f94,f86])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v1_tsep_1(sK2,sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl3_2 | spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f98,f90])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    m1_pre_topc(sK2,sK0) | m1_pre_topc(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f98,f94,f90,f86])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~m1_pre_topc(sK2,sK0) | ~v1_tsep_1(sK2,sK0) | ~m1_pre_topc(sK1,sK0) | ~v1_tsep_1(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (1210)------------------------------
% 0.21/0.53  % (1210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1210)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (1210)Memory used [KB]: 10874
% 0.21/0.53  % (1210)Time elapsed: 0.100 s
% 0.21/0.53  % (1210)------------------------------
% 0.21/0.53  % (1210)------------------------------
% 0.21/0.53  % (1223)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (1199)Success in time 0.172 s
%------------------------------------------------------------------------------
