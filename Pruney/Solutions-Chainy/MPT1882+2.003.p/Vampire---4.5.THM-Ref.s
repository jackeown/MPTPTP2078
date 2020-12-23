%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 505 expanded)
%              Number of leaves         :   22 ( 151 expanded)
%              Depth                    :   20
%              Number of atoms          :  667 (3961 expanded)
%              Number of equality atoms :   32 (  94 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f470,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f83,f134,f141,f148,f155,f165,f200,f459,f466,f469])).

fof(f469,plain,
    ( spl5_21
    | ~ spl5_22
    | ~ spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f468,f152,f145,f331,f327])).

fof(f327,plain,
    ( spl5_21
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f331,plain,
    ( spl5_22
  <=> v1_zfmisc_1(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f145,plain,
    ( spl5_6
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f152,plain,
    ( spl5_7
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f468,plain,
    ( ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f467,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v3_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f467,plain,
    ( ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_6
    | spl5_7 ),
    inference(subsumption_resolution,[],[f371,f154])).

fof(f154,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f371,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f147,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f147,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f466,plain,
    ( spl5_21
    | spl5_22
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f465,f138,f131,f331,f327])).

fof(f131,plain,
    ( spl5_4
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f138,plain,
    ( spl5_5
  <=> v2_tex_2(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f465,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f464,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f464,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f463,f44])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f463,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f462,f45])).

fof(f45,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f462,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f461,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f461,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f427,f140])).

fof(f140,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f427,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f133,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f133,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f459,plain,
    ( ~ spl5_6
    | ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f458])).

fof(f458,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f457,f453])).

fof(f453,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl5_6 ),
    inference(resolution,[],[f369,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f369,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl5_6 ),
    inference(resolution,[],[f147,f72])).

fof(f72,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f457,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f454,f403])).

fof(f403,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl5_21 ),
    inference(resolution,[],[f108,f329])).

fof(f329,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f327])).

fof(f108,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f47,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f454,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | v1_xboole_0(k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl5_6 ),
    inference(resolution,[],[f369,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f200,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f198,f43])).

fof(f198,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f197,f44])).

fof(f197,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f196,f45])).

fof(f196,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f195,f46])).

fof(f195,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f194,f47])).

fof(f194,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f187,f81])).

fof(f81,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f187,plain,
    ( v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f184,f60])).

fof(f184,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f183,f46])).

fof(f183,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f181,f48])).

fof(f181,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f76,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f165,plain,
    ( ~ spl5_2
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f163,f43])).

fof(f163,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f162,f44])).

fof(f162,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f161,f45])).

fof(f161,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f160,f46])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f159,f47])).

fof(f159,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f158,f48])).

fof(f158,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | spl5_3 ),
    inference(subsumption_resolution,[],[f156,f80])).

fof(f80,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f156,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_3 ),
    inference(resolution,[],[f129,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f129,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f155,plain,
    ( ~ spl5_3
    | ~ spl5_7
    | spl5_1 ),
    inference(avatar_split_clause,[],[f150,f75,f152,f127])).

fof(f150,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f149,f46])).

fof(f149,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f123,f48])).

fof(f123,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f77,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f148,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_1 ),
    inference(avatar_split_clause,[],[f143,f75,f145,f127])).

fof(f143,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f142,f46])).

fof(f142,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f122,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f77,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f141,plain,
    ( ~ spl5_3
    | spl5_5
    | spl5_1 ),
    inference(avatar_split_clause,[],[f136,f75,f138,f127])).

fof(f136,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f135,f46])).

fof(f135,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f121,f48])).

fof(f121,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f134,plain,
    ( ~ spl5_3
    | spl5_4
    | spl5_1 ),
    inference(avatar_split_clause,[],[f125,f75,f131,f127])).

fof(f125,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f124,f46])).

fof(f124,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl5_1 ),
    inference(resolution,[],[f77,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f49,f79,f75])).

fof(f49,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

% (10985)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f82,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f50,f79,f75])).

fof(f50,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (10987)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (10991)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.50  % (10986)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (10977)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (10995)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (10975)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (10986)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (10976)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f470,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f82,f83,f134,f141,f148,f155,f165,f200,f459,f466,f469])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    spl5_21 | ~spl5_22 | ~spl5_6 | spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f468,f152,f145,f331,f327])).
% 0.21/0.52  fof(f327,plain,(
% 0.21/0.52    spl5_21 <=> v1_xboole_0(sK2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.52  fof(f331,plain,(
% 0.21/0.52    spl5_22 <=> v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl5_6 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl5_7 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f468,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | (~spl5_6 | spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f467,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ~v1_xboole_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f26,f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.52  fof(f467,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | (~spl5_6 | spl5_7)),
% 0.21/0.52    inference(subsumption_resolution,[],[f371,f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f371,plain,(
% 0.21/0.52    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f147,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f145])).
% 0.21/0.52  fof(f466,plain,(
% 0.21/0.52    spl5_21 | spl5_22 | ~spl5_4 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f465,f138,f131,f331,f327])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    spl5_4 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl5_5 <=> v2_tex_2(sK2(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f465,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f464,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f464,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f463,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f463,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f462,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    v2_tdlat_3(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f462,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f461,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f461,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f427,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f138])).
% 0.21/0.52  fof(f427,plain,(
% 0.21/0.52    v1_zfmisc_1(sK2(sK0,sK1)) | ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f133,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f131])).
% 0.21/0.52  fof(f459,plain,(
% 0.21/0.52    ~spl5_6 | ~spl5_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f458])).
% 0.21/0.52  fof(f458,plain,(
% 0.21/0.52    $false | (~spl5_6 | ~spl5_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f457,f453])).
% 0.21/0.52  fof(f453,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_zfmisc_1(sK2(sK0,sK1))) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f369,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(rectify,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f369,plain,(
% 0.21/0.52    r2_hidden(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f147,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.52  fof(f457,plain,(
% 0.21/0.52    v1_xboole_0(k1_zfmisc_1(sK2(sK0,sK1))) | (~spl5_6 | ~spl5_21)),
% 0.21/0.52    inference(subsumption_resolution,[],[f454,f403])).
% 0.21/0.52  fof(f403,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | ~spl5_21),
% 0.21/0.52    inference(resolution,[],[f108,f329])).
% 0.21/0.52  fof(f329,plain,(
% 0.21/0.52    v1_xboole_0(sK2(sK0,sK1)) | ~spl5_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f327])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(sK1,k1_zfmisc_1(X2))) )),
% 0.21/0.52    inference(resolution,[],[f47,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.52  fof(f454,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | v1_xboole_0(k1_zfmisc_1(sK2(sK0,sK1))) | ~spl5_6),
% 0.21/0.52    inference(resolution,[],[f369,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~spl5_1 | spl5_2),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    $false | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f198,f43])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    v2_struct_0(sK0) | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f197,f44])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f196,f45])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f195,f46])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f194,f47])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f193,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_1 | spl5_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f187,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl5_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl5_1),
% 0.21/0.52    inference(resolution,[],[f184,f60])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    v2_tex_2(sK1,sK0) | ~spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f183,f46])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f181,f48])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.52    inference(resolution,[],[f76,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    v3_tex_2(sK1,sK0) | ~spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl5_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~spl5_2 | spl5_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    $false | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f163,f43])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    v2_struct_0(sK0) | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f162,f44])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f161,f45])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f46])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f47])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f158,f48])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_2 | spl5_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f156,f80])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    v1_zfmisc_1(sK1) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f79])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | spl5_3),
% 0.21/0.52    inference(resolution,[],[f129,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ~v2_tex_2(sK1,sK0) | spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f127])).
% 0.21/0.52  fof(f127,plain,(
% 0.21/0.52    spl5_3 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ~spl5_3 | ~spl5_7 | spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f150,f75,f152,f127])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f149,f46])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f123,f48])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f77,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ~v3_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ~spl5_3 | spl5_6 | spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f143,f75,f145,f127])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f142,f46])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f122,f48])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f77,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~spl5_3 | spl5_5 | spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f136,f75,f138,f127])).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f135,f46])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f121,f48])).
% 1.20/0.52  fof(f121,plain,(
% 1.20/0.52    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_1),
% 1.20/0.52    inference(resolution,[],[f77,f55])).
% 1.20/0.52  fof(f55,plain,(
% 1.20/0.52    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f32])).
% 1.20/0.52  fof(f134,plain,(
% 1.20/0.52    ~spl5_3 | spl5_4 | spl5_1),
% 1.20/0.52    inference(avatar_split_clause,[],[f125,f75,f131,f127])).
% 1.20/0.52  fof(f125,plain,(
% 1.20/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | spl5_1),
% 1.20/0.52    inference(subsumption_resolution,[],[f124,f46])).
% 1.20/0.52  fof(f124,plain,(
% 1.20/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl5_1),
% 1.20/0.52    inference(subsumption_resolution,[],[f120,f48])).
% 1.20/0.52  fof(f120,plain,(
% 1.20/0.52    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl5_1),
% 1.20/0.52    inference(resolution,[],[f77,f54])).
% 1.20/0.52  fof(f54,plain,(
% 1.20/0.52    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f32])).
% 1.20/0.52  fof(f83,plain,(
% 1.20/0.52    spl5_1 | spl5_2),
% 1.20/0.52    inference(avatar_split_clause,[],[f49,f79,f75])).
% 1.20/0.52  fof(f49,plain,(
% 1.20/0.52    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f27])).
% 1.20/0.52  % (10985)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.20/0.52  fof(f82,plain,(
% 1.20/0.52    ~spl5_1 | ~spl5_2),
% 1.20/0.52    inference(avatar_split_clause,[],[f50,f79,f75])).
% 1.20/0.52  fof(f50,plain,(
% 1.20/0.52    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 1.20/0.52    inference(cnf_transformation,[],[f27])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (10986)------------------------------
% 1.20/0.52  % (10986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (10986)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (10986)Memory used [KB]: 10746
% 1.20/0.52  % (10986)Time elapsed: 0.099 s
% 1.20/0.52  % (10986)------------------------------
% 1.20/0.52  % (10986)------------------------------
% 1.20/0.52  % (10974)Success in time 0.153 s
%------------------------------------------------------------------------------
