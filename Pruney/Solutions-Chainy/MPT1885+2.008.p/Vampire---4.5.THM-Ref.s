%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 170 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  345 ( 930 expanded)
%              Number of equality atoms :   24 (  82 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f197,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f73,f98,f109,f114,f188,f192,f194,f196])).

fof(f196,plain,
    ( ~ spl2_8
    | spl2_11 ),
    inference(avatar_split_clause,[],[f195,f95,f85])).

fof(f85,plain,
    ( spl2_8
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f95,plain,
    ( spl2_11
  <=> l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f195,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_11 ),
    inference(resolution,[],[f96,f33])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f96,plain,
    ( ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f194,plain,
    ( ~ spl2_4
    | ~ spl2_2
    | spl2_12 ),
    inference(avatar_split_clause,[],[f193,f101,f49,f57])).

fof(f57,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f49,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f101,plain,
    ( spl2_12
  <=> v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f193,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_12 ),
    inference(resolution,[],[f102,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f102,plain,
    ( ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f192,plain,
    ( ~ spl2_4
    | ~ spl2_2
    | spl2_13 ),
    inference(avatar_split_clause,[],[f191,f104,f49,f57])).

fof(f104,plain,
    ( spl2_13
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f191,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_13 ),
    inference(resolution,[],[f105,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f188,plain,
    ( spl2_5
    | ~ spl2_4
    | ~ spl2_13
    | spl2_14
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f185,f71,f45,f107,f104,f57,f61])).

fof(f61,plain,
    ( spl2_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f107,plain,
    ( spl2_14
  <=> v4_tex_2(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f45,plain,
    ( spl2_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f71,plain,
    ( spl2_6
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f185,plain,
    ( v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(resolution,[],[f184,f46])).

fof(f46,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f184,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(sK1,X0)
        | v4_tex_2(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl2_6 ),
    inference(superposition,[],[f65,f72])).

fof(f72,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(u1_struct_0(X1),X0)
      | v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f114,plain,
    ( ~ spl2_2
    | ~ spl2_4
    | spl2_8 ),
    inference(avatar_split_clause,[],[f112,f85,f57,f49])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_8 ),
    inference(resolution,[],[f110,f41])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | spl2_8 ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f86,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f109,plain,
    ( spl2_10
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f83,f71,f107,f104,f101,f92])).

fof(f92,plain,
    ( spl2_10
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f83,plain,
    ( ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_6 ),
    inference(trivial_inequality_removal,[],[f82])).

fof(f82,plain,
    ( sK1 != sK1
    | ~ v4_tex_2(k1_pre_topc(sK0,sK1),sK0)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_6 ),
    inference(superposition,[],[f32,f72])).

fof(f32,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK1
      | ~ v4_tex_2(X2,sK0)
      | ~ m1_pre_topc(X2,sK0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK1
        | ~ v4_tex_2(X2,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v3_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,sK0)
              | ~ m1_pre_topc(X2,sK0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ v4_tex_2(X2,sK0)
            | ~ m1_pre_topc(X2,sK0)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v3_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK1
          | ~ v4_tex_2(X2,sK0)
          | ~ m1_pre_topc(X2,sK0)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v3_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).

fof(f98,plain,
    ( ~ spl2_10
    | ~ spl2_11
    | spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f81,f71,f53,f95,f92])).

fof(f53,plain,
    ( spl2_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f81,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_6 ),
    inference(superposition,[],[f39,f72])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f73,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f68,f57,f49,f71])).

fof(f68,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl2_4 ),
    inference(resolution,[],[f36,f58])).

fof(f58,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f63,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f28,f57])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f30,f49])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f31,f45])).

fof(f31,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (13269)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (13271)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (13261)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (13263)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (13275)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (13264)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (13261)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (13275)Refutation not found, incomplete strategy% (13275)------------------------------
% 0.22/0.49  % (13275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13275)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (13275)Memory used [KB]: 10618
% 0.22/0.49  % (13275)Time elapsed: 0.068 s
% 0.22/0.49  % (13275)------------------------------
% 0.22/0.49  % (13275)------------------------------
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f47,f51,f55,f59,f63,f73,f98,f109,f114,f188,f192,f194,f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ~spl2_8 | spl2_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f195,f95,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl2_8 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl2_11 <=> l1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_11),
% 0.22/0.49    inference(resolution,[],[f96,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~l1_struct_0(k1_pre_topc(sK0,sK1)) | spl2_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f95])).
% 0.22/0.49  fof(f194,plain,(
% 0.22/0.49    ~spl2_4 | ~spl2_2 | spl2_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f193,f101,f49,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl2_4 <=> l1_pre_topc(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    spl2_12 <=> v1_pre_topc(k1_pre_topc(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_12),
% 0.22/0.49    inference(resolution,[],[f102,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f101])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    ~spl2_4 | ~spl2_2 | spl2_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f191,f104,f49,f57])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl2_13 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_13),
% 0.22/0.49    inference(resolution,[],[f105,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | spl2_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f104])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    spl2_5 | ~spl2_4 | ~spl2_13 | spl2_14 | ~spl2_1 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f185,f71,f45,f107,f104,f57,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    spl2_5 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl2_14 <=> v4_tex_2(k1_pre_topc(sK0,sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    spl2_1 <=> v3_tex_2(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl2_6 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_1 | ~spl2_6)),
% 0.22/0.49    inference(resolution,[],[f184,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    v3_tex_2(sK1,sK0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f45])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_tex_2(sK1,X0) | v4_tex_2(k1_pre_topc(sK0,sK1),X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl2_6),
% 0.22/0.49    inference(superposition,[],[f65,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f71])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_tex_2(u1_struct_0(X1),X0) | v4_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(global_subsumption,[],[f35,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(u1_struct_0(X1),X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tex_2(X2,X0) | ~v4_tex_2(X1,X0)) & (v4_tex_2(X1,X0) | ~v3_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v3_tex_2(X2,X0) <=> v4_tex_2(X1,X0))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ~spl2_2 | ~spl2_4 | spl2_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f112,f85,f57,f49])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f111])).
% 0.22/0.49  fof(f111,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_8),
% 0.22/0.49    inference(resolution,[],[f110,f41])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | spl2_8),
% 0.22/0.49    inference(resolution,[],[f86,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | spl2_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    spl2_10 | ~spl2_12 | ~spl2_13 | ~spl2_14 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f83,f71,f107,f104,f101,f92])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl2_10 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_6),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    sK1 != sK1 | ~v4_tex_2(k1_pre_topc(sK0,sK1),sK0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~v1_pre_topc(k1_pre_topc(sK0,sK1)) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_6),
% 0.22/0.49    inference(superposition,[],[f32,f72])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X2] : (u1_struct_0(X2) != sK1 | ~v4_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    (! [X2] : (u1_struct_0(X2) != sK1 | ~v4_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f24,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => (! [X2] : (u1_struct_0(X2) != sK1 | ~v4_tex_2(X2,sK0) | ~m1_pre_topc(X2,sK0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_tex_2)).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~spl2_10 | ~spl2_11 | spl2_3 | ~spl2_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f81,f71,f53,f95,f92])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl2_3 <=> v1_xboole_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl2_6),
% 0.22/0.49    inference(superposition,[],[f39,f72])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl2_6 | ~spl2_2 | ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f68,f57,f49,f71])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl2_2 | ~spl2_4)),
% 0.22/0.49    inference(resolution,[],[f66,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl2_4),
% 0.22/0.49    inference(resolution,[],[f36,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    l1_pre_topc(sK0) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f57])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ~spl2_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f27,f61])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f28,f57])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ~spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f29,f53])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~v1_xboole_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f30,f49])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f45])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v3_tex_2(sK1,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (13261)------------------------------
% 0.22/0.49  % (13261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (13261)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (13261)Memory used [KB]: 10746
% 0.22/0.49  % (13261)Time elapsed: 0.067 s
% 0.22/0.49  % (13261)------------------------------
% 0.22/0.49  % (13261)------------------------------
% 0.22/0.49  % (13254)Success in time 0.132 s
%------------------------------------------------------------------------------
