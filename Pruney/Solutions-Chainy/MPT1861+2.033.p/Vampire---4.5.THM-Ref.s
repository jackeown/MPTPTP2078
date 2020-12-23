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
% DateTime   : Thu Dec  3 13:20:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 251 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :    8
%              Number of atoms          :  299 ( 873 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f766,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f61,f66,f80,f102,f141,f164,f181,f192,f333,f394,f451,f465,f477,f740,f765])).

fof(f765,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_35
    | spl3_43
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f764])).

fof(f764,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_20
    | ~ spl3_35
    | spl3_43
    | ~ spl3_45 ),
    inference(global_subsumption,[],[f25,f726,f729])).

fof(f729,plain,
    ( ~ v2_tex_2(sK2,sK0)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_20
    | spl3_43
    | ~ spl3_45 ),
    inference(unit_resulting_resolution,[],[f41,f51,f180,f464,f476,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f476,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl3_45
  <=> ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f464,plain,
    ( ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f462])).

fof(f462,plain,
    ( spl3_43
  <=> v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f180,plain,
    ( ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl3_20
  <=> ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f51,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f41,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f726,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_35
    | spl3_43
    | ~ spl3_45 ),
    inference(unit_resulting_resolution,[],[f41,f46,f393,f464,f476,f27])).

fof(f393,plain,
    ( ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),X0)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl3_35
  <=> ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f46,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f25,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & ( v2_tex_2(X2,sK0)
                | v2_tex_2(X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & ( v2_tex_2(X2,sK0)
              | v2_tex_2(X1,sK0) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & ( v2_tex_2(X2,sK0)
            | v2_tex_2(sK1,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & ( v2_tex_2(X2,sK0)
          | v2_tex_2(sK1,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & ( v2_tex_2(sK2,sK0)
        | v2_tex_2(sK1,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f740,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20
    | spl3_43
    | ~ spl3_45 ),
    inference(avatar_contradiction_clause,[],[f739])).

fof(f739,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20
    | spl3_43
    | ~ spl3_45 ),
    inference(global_subsumption,[],[f22,f730])).

fof(f730,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_20
    | spl3_43
    | ~ spl3_45 ),
    inference(unit_resulting_resolution,[],[f60,f51,f180,f464,f476,f27])).

fof(f60,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_5
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

% (31140)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
fof(f477,plain,
    ( spl3_45
    | ~ spl3_22
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f458,f449,f190,f475])).

fof(f190,plain,
    ( spl3_22
  <=> ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f449,plain,
    ( spl3_41
  <=> ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f458,plain,
    ( ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_22
    | ~ spl3_41 ),
    inference(superposition,[],[f191,f450])).

fof(f450,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f449])).

fof(f191,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f190])).

fof(f465,plain,
    ( ~ spl3_43
    | spl3_6
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f456,f449,f63,f462])).

fof(f63,plain,
    ( spl3_6
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f456,plain,
    ( ~ v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)
    | spl3_6
    | ~ spl3_41 ),
    inference(superposition,[],[f65,f450])).

fof(f65,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f451,plain,
    ( spl3_41
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f322,f138,f49,f449])).

fof(f138,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f322,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f298,f304])).

fof(f304,plain,
    ( ! [X0] : k9_subset_1(sK2,X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f140,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f298,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f51,f37])).

fof(f394,plain,
    ( spl3_35
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f377,f331,f392])).

fof(f331,plain,
    ( spl3_30
  <=> ! [X0] : k9_subset_1(sK2,X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f377,plain,
    ( ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),X0)
    | ~ spl3_30 ),
    inference(superposition,[],[f35,f332])).

fof(f332,plain,
    ( ! [X0] : k9_subset_1(sK2,X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f331])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f333,plain,
    ( spl3_30
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f304,f138,f331])).

fof(f192,plain,
    ( spl3_22
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f153,f49,f190])).

fof(f153,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f51,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f181,plain,
    ( spl3_20
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f176,f162,f179])).

fof(f162,plain,
    ( spl3_18
  <=> ! [X0] : m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f176,plain,
    ( ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),sK2)
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f163,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f163,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f164,plain,
    ( spl3_18
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f155,f138,f162])).

fof(f155,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2))
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f140,f33])).

fof(f141,plain,
    ( spl3_15
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f127,f99,f138])).

fof(f99,plain,
    ( spl3_10
  <=> sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | ~ spl3_10 ),
    inference(superposition,[],[f81,f101])).

fof(f101,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f99])).

fof(f81,plain,(
    ! [X0,X1] : m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f89,f77,f99])).

fof(f77,plain,
    ( spl3_8
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f89,plain,
    ( sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f79,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f79,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl3_8
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f68,f49,f77])).

fof(f68,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f51,f31])).

fof(f66,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f61,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f25,f58,f54])).

fof(f54,plain,
    ( spl3_4
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:12:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.43  % (31148)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.45  % (31148)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f766,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(avatar_sat_refutation,[],[f42,f47,f52,f61,f66,f80,f102,f141,f164,f181,f192,f333,f394,f451,f465,f477,f740,f765])).
% 0.22/0.45  fof(f765,plain,(
% 0.22/0.45    ~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_20 | ~spl3_35 | spl3_43 | ~spl3_45),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f764])).
% 0.22/0.45  fof(f764,plain,(
% 0.22/0.45    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_20 | ~spl3_35 | spl3_43 | ~spl3_45)),
% 0.22/0.45    inference(global_subsumption,[],[f25,f726,f729])).
% 0.22/0.45  fof(f729,plain,(
% 0.22/0.45    ~v2_tex_2(sK2,sK0) | (~spl3_1 | ~spl3_3 | ~spl3_20 | spl3_43 | ~spl3_45)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f41,f51,f180,f464,f476,f27])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,axiom,(
% 0.22/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.22/0.45  fof(f476,plain,(
% 0.22/0.45    ( ! [X1] : (m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_45),
% 0.22/0.45    inference(avatar_component_clause,[],[f475])).
% 0.22/0.45  fof(f475,plain,(
% 0.22/0.45    spl3_45 <=> ! [X1] : m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.22/0.45  fof(f464,plain,(
% 0.22/0.45    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | spl3_43),
% 0.22/0.45    inference(avatar_component_clause,[],[f462])).
% 0.22/0.45  fof(f462,plain,(
% 0.22/0.45    spl3_43 <=> v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.22/0.45  fof(f180,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k9_subset_1(sK2,X0,sK2),sK2)) ) | ~spl3_20),
% 0.22/0.45    inference(avatar_component_clause,[],[f179])).
% 0.22/0.45  fof(f179,plain,(
% 0.22/0.45    spl3_20 <=> ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.45  fof(f51,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.22/0.45    inference(avatar_component_clause,[],[f49])).
% 0.22/0.45  fof(f49,plain,(
% 0.22/0.45    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.45  fof(f41,plain,(
% 0.22/0.45    l1_pre_topc(sK0) | ~spl3_1),
% 0.22/0.45    inference(avatar_component_clause,[],[f39])).
% 0.22/0.45  fof(f39,plain,(
% 0.22/0.45    spl3_1 <=> l1_pre_topc(sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.45  fof(f726,plain,(
% 0.22/0.45    ~v2_tex_2(sK1,sK0) | (~spl3_1 | ~spl3_2 | ~spl3_35 | spl3_43 | ~spl3_45)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f41,f46,f393,f464,f476,f27])).
% 0.22/0.45  fof(f393,plain,(
% 0.22/0.45    ( ! [X0] : (r1_tarski(k9_subset_1(sK2,X0,sK2),X0)) ) | ~spl3_35),
% 0.22/0.45    inference(avatar_component_clause,[],[f392])).
% 0.22/0.45  fof(f392,plain,(
% 0.22/0.45    spl3_35 <=> ! [X0] : r1_tarski(k9_subset_1(sK2,X0,sK2),X0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.45  fof(f46,plain,(
% 0.22/0.45    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 0.22/0.45    inference(avatar_component_clause,[],[f44])).
% 0.22/0.45  fof(f44,plain,(
% 0.22/0.45    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19,f18,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.45    inference(ennf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,negated_conjecture,(
% 0.22/0.45    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.45    inference(negated_conjecture,[],[f8])).
% 0.22/0.45  fof(f8,conjecture,(
% 0.22/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.22/0.45  fof(f740,plain,(
% 0.22/0.45    ~spl3_3 | ~spl3_5 | ~spl3_20 | spl3_43 | ~spl3_45),
% 0.22/0.45    inference(avatar_contradiction_clause,[],[f739])).
% 0.22/0.45  fof(f739,plain,(
% 0.22/0.45    $false | (~spl3_3 | ~spl3_5 | ~spl3_20 | spl3_43 | ~spl3_45)),
% 0.22/0.45    inference(global_subsumption,[],[f22,f730])).
% 0.22/0.45  fof(f730,plain,(
% 0.22/0.45    ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_5 | ~spl3_20 | spl3_43 | ~spl3_45)),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f60,f51,f180,f464,f476,f27])).
% 0.22/0.45  fof(f60,plain,(
% 0.22/0.45    v2_tex_2(sK2,sK0) | ~spl3_5),
% 0.22/0.45    inference(avatar_component_clause,[],[f58])).
% 0.22/0.45  fof(f58,plain,(
% 0.22/0.45    spl3_5 <=> v2_tex_2(sK2,sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    l1_pre_topc(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f20])).
% 0.22/0.45  % (31140)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.45  fof(f477,plain,(
% 0.22/0.45    spl3_45 | ~spl3_22 | ~spl3_41),
% 0.22/0.45    inference(avatar_split_clause,[],[f458,f449,f190,f475])).
% 0.22/0.45  fof(f190,plain,(
% 0.22/0.45    spl3_22 <=> ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.45  fof(f449,plain,(
% 0.22/0.45    spl3_41 <=> ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.22/0.45  fof(f458,plain,(
% 0.22/0.45    ( ! [X1] : (m1_subset_1(k9_subset_1(sK2,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_22 | ~spl3_41)),
% 0.22/0.45    inference(superposition,[],[f191,f450])).
% 0.22/0.45  fof(f450,plain,(
% 0.22/0.45    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)) ) | ~spl3_41),
% 0.22/0.45    inference(avatar_component_clause,[],[f449])).
% 0.22/0.45  fof(f191,plain,(
% 0.22/0.45    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_22),
% 0.22/0.45    inference(avatar_component_clause,[],[f190])).
% 0.22/0.45  fof(f465,plain,(
% 0.22/0.45    ~spl3_43 | spl3_6 | ~spl3_41),
% 0.22/0.45    inference(avatar_split_clause,[],[f456,f449,f63,f462])).
% 0.22/0.45  fof(f63,plain,(
% 0.22/0.45    spl3_6 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.45  fof(f456,plain,(
% 0.22/0.45    ~v2_tex_2(k9_subset_1(sK2,sK1,sK2),sK0) | (spl3_6 | ~spl3_41)),
% 0.22/0.45    inference(superposition,[],[f65,f450])).
% 0.22/0.45  fof(f65,plain,(
% 0.22/0.45    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_6),
% 0.22/0.45    inference(avatar_component_clause,[],[f63])).
% 0.22/0.45  fof(f451,plain,(
% 0.22/0.45    spl3_41 | ~spl3_3 | ~spl3_15),
% 0.22/0.45    inference(avatar_split_clause,[],[f322,f138,f49,f449])).
% 0.22/0.45  fof(f138,plain,(
% 0.22/0.45    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 0.22/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.45  fof(f322,plain,(
% 0.22/0.45    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)) ) | (~spl3_3 | ~spl3_15)),
% 0.22/0.45    inference(forward_demodulation,[],[f298,f304])).
% 0.22/0.45  fof(f304,plain,(
% 0.22/0.45    ( ! [X0] : (k9_subset_1(sK2,X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_15),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f140,f37])).
% 0.22/0.45  fof(f37,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.22/0.45    inference(definition_unfolding,[],[f34,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,axiom,(
% 0.22/0.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,axiom,(
% 0.22/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.45  fof(f140,plain,(
% 0.22/0.45    m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~spl3_15),
% 0.22/0.45    inference(avatar_component_clause,[],[f138])).
% 0.22/0.45  fof(f298,plain,(
% 0.22/0.45    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_3),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f51,f37])).
% 0.22/0.45  fof(f394,plain,(
% 0.22/0.45    spl3_35 | ~spl3_30),
% 0.22/0.45    inference(avatar_split_clause,[],[f377,f331,f392])).
% 0.22/0.46  fof(f331,plain,(
% 0.22/0.46    spl3_30 <=> ! [X0] : k9_subset_1(sK2,X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.46  fof(f377,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k9_subset_1(sK2,X0,sK2),X0)) ) | ~spl3_30),
% 0.22/0.46    inference(superposition,[],[f35,f332])).
% 0.22/0.46  fof(f332,plain,(
% 0.22/0.46    ( ! [X0] : (k9_subset_1(sK2,X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) ) | ~spl3_30),
% 0.22/0.46    inference(avatar_component_clause,[],[f331])).
% 0.22/0.46  fof(f35,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.46    inference(definition_unfolding,[],[f28,f29])).
% 0.22/0.46  fof(f28,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.46  fof(f333,plain,(
% 0.22/0.46    spl3_30 | ~spl3_15),
% 0.22/0.46    inference(avatar_split_clause,[],[f304,f138,f331])).
% 0.22/0.46  fof(f192,plain,(
% 0.22/0.46    spl3_22 | ~spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f153,f49,f190])).
% 0.22/0.46  fof(f153,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_3),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f51,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(cnf_transformation,[],[f15])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.22/0.46  fof(f181,plain,(
% 0.22/0.46    spl3_20 | ~spl3_18),
% 0.22/0.46    inference(avatar_split_clause,[],[f176,f162,f179])).
% 0.22/0.46  fof(f162,plain,(
% 0.22/0.46    spl3_18 <=> ! [X0] : m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.46  fof(f176,plain,(
% 0.22/0.46    ( ! [X0] : (r1_tarski(k9_subset_1(sK2,X0,sK2),sK2)) ) | ~spl3_18),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f163,f31])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f21,plain,(
% 0.22/0.46    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.46    inference(nnf_transformation,[],[f6])).
% 0.22/0.46  fof(f6,axiom,(
% 0.22/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.46  fof(f163,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2))) ) | ~spl3_18),
% 0.22/0.46    inference(avatar_component_clause,[],[f162])).
% 0.22/0.46  fof(f164,plain,(
% 0.22/0.46    spl3_18 | ~spl3_15),
% 0.22/0.46    inference(avatar_split_clause,[],[f155,f138,f162])).
% 0.22/0.46  fof(f155,plain,(
% 0.22/0.46    ( ! [X0] : (m1_subset_1(k9_subset_1(sK2,X0,sK2),k1_zfmisc_1(sK2))) ) | ~spl3_15),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f140,f33])).
% 0.22/0.46  fof(f141,plain,(
% 0.22/0.46    spl3_15 | ~spl3_10),
% 0.22/0.46    inference(avatar_split_clause,[],[f127,f99,f138])).
% 0.22/0.46  fof(f99,plain,(
% 0.22/0.46    spl3_10 <=> sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0)))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.46  fof(f127,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(sK2)) | ~spl3_10),
% 0.22/0.46    inference(superposition,[],[f81,f101])).
% 0.22/0.46  fof(f101,plain,(
% 0.22/0.46    sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0))) | ~spl3_10),
% 0.22/0.46    inference(avatar_component_clause,[],[f99])).
% 0.22/0.46  fof(f81,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,X1)),k1_zfmisc_1(X0))) )),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f35,f32])).
% 0.22/0.46  fof(f32,plain,(
% 0.22/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f21])).
% 0.22/0.46  fof(f102,plain,(
% 0.22/0.46    spl3_10 | ~spl3_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f89,f77,f99])).
% 0.22/0.46  fof(f77,plain,(
% 0.22/0.46    spl3_8 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.46  fof(f89,plain,(
% 0.22/0.46    sK2 = k1_setfam_1(k2_tarski(sK2,u1_struct_0(sK0))) | ~spl3_8),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f79,f36])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.22/0.46    inference(definition_unfolding,[],[f30,f29])).
% 0.22/0.46  fof(f30,plain,(
% 0.22/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.46  fof(f79,plain,(
% 0.22/0.46    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f77])).
% 0.22/0.46  fof(f80,plain,(
% 0.22/0.46    spl3_8 | ~spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f68,f49,f77])).
% 0.22/0.46  fof(f68,plain,(
% 0.22/0.46    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_3),
% 0.22/0.46    inference(unit_resulting_resolution,[],[f51,f31])).
% 0.22/0.46  fof(f66,plain,(
% 0.22/0.46    ~spl3_6),
% 0.22/0.46    inference(avatar_split_clause,[],[f26,f63])).
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    spl3_4 | spl3_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f25,f58,f54])).
% 0.22/0.46  fof(f54,plain,(
% 0.22/0.46    spl3_4 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.46  fof(f52,plain,(
% 0.22/0.46    spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f24,f49])).
% 0.22/0.46  fof(f24,plain,(
% 0.22/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f47,plain,(
% 0.22/0.46    spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.46    inference(cnf_transformation,[],[f20])).
% 0.22/0.46  fof(f42,plain,(
% 0.22/0.46    spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f22,f39])).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (31148)------------------------------
% 0.22/0.46  % (31148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (31148)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (31148)Memory used [KB]: 11257
% 0.22/0.46  % (31148)Time elapsed: 0.049 s
% 0.22/0.46  % (31148)------------------------------
% 0.22/0.46  % (31148)------------------------------
% 0.22/0.46  % (31130)Success in time 0.1 s
%------------------------------------------------------------------------------
