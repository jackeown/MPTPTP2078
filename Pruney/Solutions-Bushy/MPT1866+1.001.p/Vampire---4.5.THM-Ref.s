%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1866+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:47 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 164 expanded)
%              Number of leaves         :   17 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  354 (1050 expanded)
%              Number of equality atoms :   28 ( 101 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f39,f43,f47,f51,f59,f85,f89,f91,f96,f100,f102])).

fof(f102,plain,
    ( spl3_5
    | ~ spl3_4
    | spl3_3
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f101,f64,f37,f41,f45,f49])).

fof(f49,plain,
    ( spl3_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f45,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,
    ( spl3_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( spl3_7
  <=> v2_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f101,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK2(X0,X1)) = X1
            & m1_pre_topc(sK2(X0,X1),X0)
            & v1_pre_topc(sK2(X0,X1))
            & ~ v2_struct_0(sK2(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK2(X0,X1)) = X1
        & m1_pre_topc(sK2(X0,X1),X0)
        & v1_pre_topc(sK2(X0,X1))
        & ~ v2_struct_0(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f65,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f100,plain,
    ( ~ spl3_2
    | ~ spl3_13
    | spl3_7
    | spl3_12
    | ~ spl3_1
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f97,f94,f57,f33,f80,f64,f83,f37])).

fof(f83,plain,
    ( spl3_13
  <=> m1_pre_topc(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f80,plain,
    ( spl3_12
  <=> v1_tdlat_3(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f33,plain,
    ( spl3_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_6
  <=> sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ v2_tex_2(u1_struct_0(X0),sK0)
        | v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f97,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(superposition,[],[f95,f58])).

fof(f58,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(u1_struct_0(X0),sK0)
        | v1_tdlat_3(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl3_5
    | spl3_14
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f92,f45,f94,f49])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(u1_struct_0(X0),sK0)
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v1_tdlat_3(X0)
        | v2_struct_0(sK0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v1_tdlat_3(X1)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f91,plain,
    ( spl3_5
    | ~ spl3_4
    | spl3_3
    | ~ spl3_2
    | spl3_11 ),
    inference(avatar_split_clause,[],[f90,f77,f37,f41,f45,f49])).

fof(f77,plain,
    ( spl3_11
  <=> v1_pre_topc(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_11 ),
    inference(resolution,[],[f78,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK2(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,
    ( ~ v1_pre_topc(sK2(sK0,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f89,plain,
    ( spl3_5
    | ~ spl3_4
    | spl3_3
    | ~ spl3_2
    | spl3_13 ),
    inference(avatar_split_clause,[],[f86,f83,f37,f41,f45,f49])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl3_13 ),
    inference(resolution,[],[f84,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f84,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f83])).

fof(f85,plain,
    ( spl3_7
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f62,f57,f83,f80,f77,f64])).

fof(f62,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ v1_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl3_6 ),
    inference(trivial_inequality_removal,[],[f61])).

fof(f61,plain,
    ( sK1 != sK1
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | ~ v1_pre_topc(sK2(sK0,sK1))
    | v2_struct_0(sK2(sK0,sK1))
    | ~ spl3_6 ),
    inference(superposition,[],[f23,f58])).

fof(f23,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK1
      | ~ m1_pre_topc(X2,sK0)
      | ~ v1_tdlat_3(X2)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK1
        | ~ m1_pre_topc(X2,sK0)
        | ~ v1_tdlat_3(X2)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_tdlat_3(X2)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,sK0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ m1_pre_topc(X2,sK0)
            | ~ v1_tdlat_3(X2)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK1
          | ~ m1_pre_topc(X2,sK0)
          | ~ v1_tdlat_3(X2)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => u1_struct_0(X2) != X1 )
                & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => u1_struct_0(X2) != X1 )
                & v2_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f59,plain,
    ( spl3_5
    | ~ spl3_4
    | spl3_6
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f53,f41,f37,f57,f45,f49])).

fof(f53,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_2
    | spl3_3 ),
    inference(resolution,[],[f52,f38])).

fof(f38,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

% (24454)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (24447)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f52,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | sK1 = u1_struct_0(sK2(X0,sK1))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl3_3 ),
    inference(resolution,[],[f27,f42])).

fof(f42,plain,
    ( ~ v1_xboole_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f47,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f22,f33])).

fof(f22,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
