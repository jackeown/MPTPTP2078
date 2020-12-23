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
% DateTime   : Thu Dec  3 13:21:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 182 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   15
%              Number of atoms          :  406 (1086 expanded)
%              Number of equality atoms :   32 ( 110 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f66,f83,f93,f103,f108,f120,f178])).

fof(f178,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_6
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f176,f65])).

fof(f65,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_6
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f176,plain,
    ( v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f175,f55])).

fof(f55,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f175,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f174,f45])).

fof(f45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f174,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_1
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f156,f40])).

fof(f40,plain,
    ( v2_tex_2(sK2,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_1
  <=> v2_tex_2(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f156,plain,
    ( ~ v2_tex_2(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | spl4_12 ),
    inference(resolution,[],[f147,f102])).

fof(f102,plain,
    ( m1_pre_topc(sK3(sK2,sK1),sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_10
  <=> m1_pre_topc(sK3(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f147,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(sK3(sK2,sK1),X3)
        | ~ v2_tex_2(sK2,X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X3) )
    | spl4_8
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f146,f92])).

fof(f92,plain,
    ( ~ v2_struct_0(sK3(sK2,sK1))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_8
  <=> v2_struct_0(sK3(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f146,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v2_tex_2(sK2,X3)
        | ~ m1_pre_topc(sK3(sK2,sK1),X3)
        | v2_struct_0(sK3(sK2,sK1))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl4_11
    | spl4_12 ),
    inference(subsumption_resolution,[],[f142,f119])).

fof(f119,plain,
    ( ~ v1_tdlat_3(sK3(sK2,sK1))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_12
  <=> v1_tdlat_3(sK3(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f142,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v2_tex_2(sK2,X3)
        | v1_tdlat_3(sK3(sK2,sK1))
        | ~ m1_pre_topc(sK3(sK2,sK1),X3)
        | v2_struct_0(sK3(sK2,sK1))
        | ~ l1_pre_topc(X3)
        | v2_struct_0(X3) )
    | ~ spl4_11 ),
    inference(superposition,[],[f36,f107])).

fof(f107,plain,
    ( sK2 = u1_struct_0(sK3(sK2,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_11
  <=> sK2 = u1_struct_0(sK3(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f10])).

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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f120,plain,
    ( ~ spl4_12
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f115,f100,f76,f117])).

fof(f76,plain,
    ( spl4_7
  <=> sP0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f115,plain,
    ( ~ v1_tdlat_3(sK3(sK2,sK1))
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f114,f78])).

fof(f78,plain,
    ( sP0(sK2,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f114,plain,
    ( ~ v1_tdlat_3(sK3(sK2,sK1))
    | ~ sP0(sK2,sK1)
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( sK2 != sK2
    | ~ v1_tdlat_3(sK3(sK2,sK1))
    | ~ sP0(sK2,sK1)
    | ~ spl4_10 ),
    inference(resolution,[],[f102,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3(X0,X1),sK1)
      | sK2 != X0
      | ~ v1_tdlat_3(sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( u1_struct_0(sK3(X0,X1)) = X0
        & m1_pre_topc(sK3(X0,X1),X1)
        & v1_pre_topc(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK3(X0,X1)) = X0
        & m1_pre_topc(sK3(X0,X1),X1)
        & v1_pre_topc(sK3(X0,X1))
        & ~ v2_struct_0(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | ~ m1_pre_topc(sK3(X0,X1),sK1)
      | ~ v1_tdlat_3(sK3(X0,X1))
      | v2_struct_0(sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f67,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X0,X1] :
      ( sK2 != X0
      | ~ m1_pre_topc(sK3(X0,X1),sK1)
      | ~ v1_tdlat_3(sK3(X0,X1))
      | ~ v1_pre_topc(sK3(X0,X1))
      | v2_struct_0(sK3(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(superposition,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK3(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK2
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_tdlat_3(X2)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK2
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_tdlat_3(X2)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v2_tex_2(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f6,f14,f13])).

fof(f13,plain,
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
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ m1_pre_topc(X2,sK1)
              | ~ v1_tdlat_3(X2)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v2_tex_2(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( u1_struct_0(X2) != X1
            | ~ m1_pre_topc(X2,sK1)
            | ~ v1_tdlat_3(X2)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v2_tex_2(X1,sK1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
        & ~ v1_xboole_0(X1) )
   => ( ! [X2] :
          ( u1_struct_0(X2) != sK2
          | ~ m1_pre_topc(X2,sK1)
          | ~ v1_tdlat_3(X2)
          | ~ v1_pre_topc(X2)
          | v2_struct_0(X2) )
      & v2_tex_2(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

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
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
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
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f108,plain,
    ( spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f85,f76,f105])).

fof(f85,plain,
    ( sK2 = u1_struct_0(sK3(sK2,sK1))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f78,f31])).

fof(f103,plain,
    ( spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f86,f76,f100])).

fof(f86,plain,
    ( m1_pre_topc(sK3(sK2,sK1),sK1)
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f78,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK3(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,
    ( ~ spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f88,f76,f90])).

fof(f88,plain,
    ( ~ v2_struct_0(sK3(sK2,sK1))
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f78,f28])).

fof(f83,plain,
    ( spl4_7
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f82,f63,f53,f48,f43,f76])).

fof(f48,plain,
    ( spl4_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f82,plain,
    ( sP0(sK2,sK1)
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f81,f65])).

fof(f81,plain,
    ( sP0(sK2,sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f80,f55])).

fof(f80,plain,
    ( sP0(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f73,f50])).

fof(f50,plain,
    ( ~ v1_xboole_0(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f73,plain,
    ( sP0(sK2,sK1)
    | v1_xboole_0(sK2)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f32,f45])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f8,f11])).

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
    inference(flattening,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f66,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f21,f63])).

fof(f21,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f41,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f26,f38])).

fof(f26,plain,(
    v2_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:18:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (8735)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.46  % (8735)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (8731)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (8731)Refutation not found, incomplete strategy% (8731)------------------------------
% 0.22/0.47  % (8731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8731)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (8731)Memory used [KB]: 6012
% 0.22/0.47  % (8731)Time elapsed: 0.002 s
% 0.22/0.47  % (8731)------------------------------
% 0.22/0.47  % (8731)------------------------------
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f179,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f41,f46,f51,f56,f66,f83,f93,f103,f108,f120,f178])).
% 0.22/0.47  fof(f178,plain,(
% 0.22/0.47    ~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_6 | spl4_8 | ~spl4_10 | ~spl4_11 | spl4_12),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.47  fof(f177,plain,(
% 0.22/0.47    $false | (~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_6 | spl4_8 | ~spl4_10 | ~spl4_11 | spl4_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f176,f65])).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    ~v2_struct_0(sK1) | spl4_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f63])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl4_6 <=> v2_struct_0(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.47  fof(f176,plain,(
% 0.22/0.47    v2_struct_0(sK1) | (~spl4_1 | ~spl4_2 | ~spl4_4 | spl4_8 | ~spl4_10 | ~spl4_11 | spl4_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f175,f55])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    l1_pre_topc(sK1) | ~spl4_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl4_4 <=> l1_pre_topc(sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.47  fof(f175,plain,(
% 0.22/0.47    ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | ~spl4_2 | spl4_8 | ~spl4_10 | ~spl4_11 | spl4_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f174,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.47  fof(f174,plain,(
% 0.22/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_1 | spl4_8 | ~spl4_10 | ~spl4_11 | spl4_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f156,f40])).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    v2_tex_2(sK2,sK1) | ~spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    spl4_1 <=> v2_tex_2(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f156,plain,(
% 0.22/0.47    ~v2_tex_2(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (spl4_8 | ~spl4_10 | ~spl4_11 | spl4_12)),
% 0.22/0.47    inference(resolution,[],[f147,f102])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    m1_pre_topc(sK3(sK2,sK1),sK1) | ~spl4_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    spl4_10 <=> m1_pre_topc(sK3(sK2,sK1),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.47  fof(f147,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_pre_topc(sK3(sK2,sK1),X3) | ~v2_tex_2(sK2,X3) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | v2_struct_0(X3)) ) | (spl4_8 | ~spl4_11 | spl4_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f146,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ~v2_struct_0(sK3(sK2,sK1)) | spl4_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f90])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    spl4_8 <=> v2_struct_0(sK3(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.47  fof(f146,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3))) | ~v2_tex_2(sK2,X3) | ~m1_pre_topc(sK3(sK2,sK1),X3) | v2_struct_0(sK3(sK2,sK1)) | ~l1_pre_topc(X3) | v2_struct_0(X3)) ) | (~spl4_11 | spl4_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f142,f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    ~v1_tdlat_3(sK3(sK2,sK1)) | spl4_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f117])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl4_12 <=> v1_tdlat_3(sK3(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    ( ! [X3] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3))) | ~v2_tex_2(sK2,X3) | v1_tdlat_3(sK3(sK2,sK1)) | ~m1_pre_topc(sK3(sK2,sK1),X3) | v2_struct_0(sK3(sK2,sK1)) | ~l1_pre_topc(X3) | v2_struct_0(X3)) ) | ~spl4_11),
% 0.22/0.47    inference(superposition,[],[f36,f107])).
% 0.22/0.47  fof(f107,plain,(
% 0.22/0.47    sK2 = u1_struct_0(sK3(sK2,sK1)) | ~spl4_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    spl4_11 <=> sK2 = u1_struct_0(sK3(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(u1_struct_0(X1),X0) | v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(equality_resolution,[],[f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    ~spl4_12 | ~spl4_7 | ~spl4_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f115,f100,f76,f117])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    spl4_7 <=> sP0(sK2,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ~v1_tdlat_3(sK3(sK2,sK1)) | (~spl4_7 | ~spl4_10)),
% 0.22/0.47    inference(subsumption_resolution,[],[f114,f78])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    sP0(sK2,sK1) | ~spl4_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f76])).
% 0.22/0.47  fof(f114,plain,(
% 0.22/0.47    ~v1_tdlat_3(sK3(sK2,sK1)) | ~sP0(sK2,sK1) | ~spl4_10),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f113])).
% 0.22/0.47  fof(f113,plain,(
% 0.22/0.47    sK2 != sK2 | ~v1_tdlat_3(sK3(sK2,sK1)) | ~sP0(sK2,sK1) | ~spl4_10),
% 0.22/0.47    inference(resolution,[],[f102,f69])).
% 0.22/0.47  fof(f69,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_pre_topc(sK3(X0,X1),sK1) | sK2 != X0 | ~v1_tdlat_3(sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f68,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : ((u1_struct_0(sK3(X0,X1)) = X0 & m1_pre_topc(sK3(X0,X1),X1) & v1_pre_topc(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))) | ~sP0(X0,X1))),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK3(X0,X1)) = X0 & m1_pre_topc(sK3(X0,X1),X1) & v1_pre_topc(sK3(X0,X1)) & ~v2_struct_0(sK3(X0,X1))))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~sP0(X0,X1))),
% 0.22/0.47    inference(rectify,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~sP0(X1,X0))),
% 0.22/0.47    inference(nnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~sP0(X1,X0))),
% 0.22/0.47    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sK2 != X0 | ~m1_pre_topc(sK3(X0,X1),sK1) | ~v1_tdlat_3(sK3(X0,X1)) | v2_struct_0(sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f67,f29])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_pre_topc(sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ( ! [X0,X1] : (sK2 != X0 | ~m1_pre_topc(sK3(X0,X1),sK1) | ~v1_tdlat_3(sK3(X0,X1)) | ~v1_pre_topc(sK3(X0,X1)) | v2_struct_0(sK3(X0,X1)) | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(superposition,[],[f27,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (u1_struct_0(sK3(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X2] : (u1_struct_0(X2) != sK2 | ~m1_pre_topc(X2,sK1) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    (! [X2] : (u1_struct_0(X2) != sK2 | ~m1_pre_topc(X2,sK1) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v2_tex_2(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f6,f14,f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,sK1) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v2_tex_2(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,sK1) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v2_tex_2(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) => (! [X2] : (u1_struct_0(X2) != sK2 | ~m1_pre_topc(X2,sK1) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v2_tex_2(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f5])).
% 0.22/0.47  fof(f5,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((! [X2] : (u1_struct_0(X2) != X1 | (~m1_pre_topc(X2,X0) | ~v1_tdlat_3(X2) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v2_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.47    inference(negated_conjecture,[],[f3])).
% 0.22/0.47  fof(f3,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl4_11 | ~spl4_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f85,f76,f105])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    sK2 = u1_struct_0(sK3(sK2,sK1)) | ~spl4_7),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f78,f31])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    spl4_10 | ~spl4_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f86,f76,f100])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    m1_pre_topc(sK3(sK2,sK1),sK1) | ~spl4_7),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f78,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_pre_topc(sK3(X0,X1),X1) | ~sP0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    ~spl4_8 | ~spl4_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f88,f76,f90])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    ~v2_struct_0(sK3(sK2,sK1)) | ~spl4_7),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f78,f28])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    spl4_7 | ~spl4_2 | spl4_3 | ~spl4_4 | spl4_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f82,f63,f53,f48,f43,f76])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl4_3 <=> v1_xboole_0(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    sP0(sK2,sK1) | (~spl4_2 | spl4_3 | ~spl4_4 | spl4_6)),
% 0.22/0.47    inference(subsumption_resolution,[],[f81,f65])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    sP0(sK2,sK1) | v2_struct_0(sK1) | (~spl4_2 | spl4_3 | ~spl4_4)),
% 0.22/0.47    inference(subsumption_resolution,[],[f80,f55])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    sP0(sK2,sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_2 | spl4_3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f73,f50])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    ~v1_xboole_0(sK2) | spl4_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    sP0(sK2,sK1) | v1_xboole_0(sK2) | ~l1_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.22/0.47    inference(resolution,[],[f32,f45])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP0(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (sP0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(definition_folding,[],[f8,f11])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ~spl4_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f63])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ~v2_struct_0(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    spl4_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f53])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    l1_pre_topc(sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ~spl4_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f48])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ~v1_xboole_0(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl4_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f43])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl4_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f38])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    v2_tex_2(sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (8735)------------------------------
% 0.22/0.47  % (8735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8735)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (8735)Memory used [KB]: 10746
% 0.22/0.47  % (8735)Time elapsed: 0.062 s
% 0.22/0.47  % (8735)------------------------------
% 0.22/0.47  % (8735)------------------------------
% 0.22/0.47  % (8718)Success in time 0.113 s
%------------------------------------------------------------------------------
