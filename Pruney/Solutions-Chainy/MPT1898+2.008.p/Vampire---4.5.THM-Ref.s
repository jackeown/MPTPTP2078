%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 134 expanded)
%              Number of leaves         :   14 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  277 ( 559 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f121,f125])).

fof(f125,plain,(
    ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f37,f120])).

fof(f120,plain,
    ( ! [X0] : ~ l1_pre_topc(X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f119])).

% (13004)Termination reason: Refutation not found, incomplete strategy
fof(f119,plain,
    ( spl3_5
  <=> ! [X0] : ~ l1_pre_topc(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f37,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

% (13004)Memory used [KB]: 6140
fof(f27,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
    & l1_pre_topc(sK1)
    & v3_tdlat_3(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).

% (13004)Time elapsed: 0.094 s
fof(f26,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1)
      & v3_tdlat_3(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

% (13004)------------------------------
% (13004)------------------------------
fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f121,plain,
    ( spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f93,f81,f119])).

fof(f81,plain,
    ( spl3_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f93,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f91,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_tops_1(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f66,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f91,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_xboole_0))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f73,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v2_tops_1(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f88,f68])).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tops_1(X0,k1_xboole_0)
      | v2_tops_1(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f43,f40])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f73,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_xboole_0))
      | ~ v2_tops_1(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(k1_tops_1(X0,X1))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v2_tops_1(X1,X0)
        & l1_pre_topc(X0) )
     => v1_xboole_0(k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).

fof(f109,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f107,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f107,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f106,f35])).

fof(f35,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f105,f36])).

fof(f36,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f105,plain,
    ( ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f104,f37])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v3_tdlat_3(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f103,f63])).

fof(f63,plain,(
    ! [X0] : ~ sP0(sK1,X0) ),
    inference(subsumption_resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK2(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK2(X0,X1),X0)
        & r1_tarski(X1,sK2(X0,X1))
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f62,plain,(
    ! [X0] :
      ( ~ sP0(sK1,X0)
      | ~ v3_tex_2(sK2(sK1,X0),sK1) ) ),
    inference(resolution,[],[f44,f38])).

fof(f38,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_tex_2(X1,sK1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,
    ( ! [X0] :
        ( sP0(X0,k1_xboole_0)
        | ~ l1_pre_topc(X0)
        | ~ v3_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f101,f96])).

fof(f96,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_xboole_0,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f94,f83])).

fof(f83,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f94,plain,(
    ! [X0] :
      ( v2_tex_2(k1_xboole_0,X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_tex_2(k1_xboole_0,X0)
      | sP0(X0,k1_xboole_0)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f24])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:50:47 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (13004)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (12995)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (12996)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (12996)Refutation not found, incomplete strategy% (12996)------------------------------
% 0.22/0.51  % (12996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (12996)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (12996)Memory used [KB]: 6012
% 0.22/0.51  % (12996)Time elapsed: 0.093 s
% 0.22/0.51  % (12996)------------------------------
% 0.22/0.51  % (12996)------------------------------
% 0.22/0.52  % (13004)Refutation not found, incomplete strategy% (13004)------------------------------
% 0.22/0.52  % (13004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13003)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (12995)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f109,f121,f125])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ~spl3_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f124])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    $false | ~spl3_5),
% 0.22/0.52    inference(subsumption_resolution,[],[f37,f120])).
% 0.22/0.52  fof(f120,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0)) ) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f119])).
% 0.22/0.52  % (13004)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    spl3_5 <=> ! [X0] : ~l1_pre_topc(X0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    l1_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  
% 0.22/0.52  % (13004)Memory used [KB]: 6140
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).
% 0.22/0.52  % (13004)Time elapsed: 0.094 s
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1) & v3_tdlat_3(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  % (13004)------------------------------
% 0.22/0.52  % (13004)------------------------------
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    inference(negated_conjecture,[],[f10])).
% 0.22/0.52  fof(f10,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl3_5 | spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f93,f81,f119])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl3_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(superposition,[],[f91,f68])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 = k1_tops_1(X0,k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(resolution,[],[f66,f57])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.52    inference(resolution,[],[f52,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(flattening,[],[f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0] : (r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(resolution,[],[f41,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_xboole_0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f73,f90])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tops_1(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f88,f68])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (k1_xboole_0 != k1_tops_1(X0,k1_xboole_0) | v2_tops_1(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(resolution,[],[f43,f40])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.52  fof(f73,plain,(
% 0.22/0.52    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_xboole_0)) | ~v2_tops_1(k1_xboole_0,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(resolution,[],[f49,f40])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(k1_tops_1(X0,X1)) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (v1_xboole_0(k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | ~l1_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v2_tops_1(X1,X0) & l1_pre_topc(X0)) => v1_xboole_0(k1_tops_1(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc13_tops_1)).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~spl3_2),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    $false | ~spl3_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f107,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ~v2_struct_0(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    v2_struct_0(sK1) | ~spl3_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f106,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    v2_pre_topc(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl3_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f105,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    v3_tdlat_3(sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl3_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f37])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    ~l1_pre_topc(sK1) | ~v3_tdlat_3(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f103,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(sK1,X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f62,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v3_tex_2(sK2(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ! [X0,X1] : ((v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK2(X0,X1),X0) & r1_tarski(X1,sK2(X0,X1)) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0] : (~sP0(sK1,X0) | ~v3_tex_2(sK2(sK1,X0),sK1)) )),
% 0.22/0.52    inference(resolution,[],[f44,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_tex_2(X1,sK1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f27])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f31])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ( ! [X0] : (sP0(X0,k1_xboole_0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f101,f96])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl3_2),
% 0.22/0.52    inference(subsumption_resolution,[],[f94,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f81])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ( ! [X0] : (v2_tex_2(k1_xboole_0,X0) | ~v1_xboole_0(k1_xboole_0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f48,f40])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    ( ! [X0] : (~v2_tex_2(k1_xboole_0,X0) | sP0(X0,k1_xboole_0) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(resolution,[],[f47,f40])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (sP0(X0,X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(definition_folding,[],[f17,f24])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (12995)------------------------------
% 0.22/0.52  % (12995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (12995)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (12995)Memory used [KB]: 6140
% 0.22/0.52  % (12995)Time elapsed: 0.081 s
% 0.22/0.52  % (12995)------------------------------
% 0.22/0.52  % (12995)------------------------------
% 0.22/0.52  % (12990)Success in time 0.156 s
%------------------------------------------------------------------------------
