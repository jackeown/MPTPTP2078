%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 382 expanded)
%              Number of leaves         :   25 ( 113 expanded)
%              Depth                    :   19
%              Number of atoms          :  553 (2629 expanded)
%              Number of equality atoms :   43 (  80 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f660,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f105,f185,f403,f629,f647,f652,f659])).

fof(f659,plain,
    ( spl8_7
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f657,f400,f178])).

fof(f178,plain,
    ( spl8_7
  <=> v2_tex_2(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f400,plain,
    ( spl8_17
  <=> sP1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f657,plain,
    ( v2_tex_2(sK5,sK4)
    | ~ spl8_17 ),
    inference(resolution,[],[f402,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f402,plain,
    ( sP1(sK4,sK5)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f400])).

fof(f652,plain,
    ( spl8_7
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f651,f101,f178])).

fof(f101,plain,
    ( spl8_2
  <=> v1_zfmisc_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f651,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f650,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ v1_zfmisc_1(sK5)
      | ~ v3_tex_2(sK5,sK4) )
    & ( v1_zfmisc_1(sK5)
      | v3_tex_2(sK5,sK4) )
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & ~ v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_tdlat_3(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f36,f35])).

fof(f35,plain,
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
            | ~ v3_tex_2(X1,sK4) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK4) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_tdlat_3(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK4) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK4) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK5)
        | ~ v3_tex_2(sK5,sK4) )
      & ( v1_zfmisc_1(sK5)
        | v3_tex_2(sK5,sK4) )
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f650,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f649,f57])).

fof(f57,plain,(
    v2_tdlat_3(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f649,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f648,f58])).

fof(f58,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f648,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f536,f59])).

fof(f59,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f536,plain,
    ( ~ v1_zfmisc_1(sK5)
    | v2_tex_2(sK5,sK4)
    | v1_xboole_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f311,f60])).

fof(f60,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f37])).

fof(f311,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f647,plain,
    ( spl8_2
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f646,f178,f101])).

fof(f646,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5) ),
    inference(subsumption_resolution,[],[f645,f55])).

fof(f645,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f644,f57])).

fof(f644,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f304,f58])).

fof(f304,plain,
    ( ~ v2_tex_2(sK5,sK4)
    | v1_zfmisc_1(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f281,f60])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f280,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f280,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f77,f64])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f629,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl8_8 ),
    inference(subsumption_resolution,[],[f627,f59])).

fof(f627,plain,
    ( v1_xboole_0(sK5)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f626,f58])).

fof(f626,plain,
    ( ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f625,f55])).

fof(f625,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | spl8_8 ),
    inference(subsumption_resolution,[],[f620,f57])).

fof(f620,plain,
    ( ~ v2_tdlat_3(sK4)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | v1_xboole_0(sK5)
    | spl8_8 ),
    inference(resolution,[],[f604,f184])).

fof(f184,plain,
    ( ~ sP0(sK5,sK4)
    | spl8_8 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl8_8
  <=> sP0(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f604,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f307,f262])).

fof(f262,plain,(
    ! [X10,X11] :
      ( ~ v1_zfmisc_1(sK6(X10,X11))
      | v1_xboole_0(X10)
      | sP0(X10,X11) ) ),
    inference(subsumption_resolution,[],[f242,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK6(X0,X1) != X0
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK6(X0,X1) != X0
          & r1_tarski(X0,sK6(X0,X1))
          & v2_tex_2(sK6(X0,X1),X1)
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK6(X0,X1) != X0
        & r1_tarski(X0,sK6(X0,X1))
        & v2_tex_2(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f242,plain,(
    ! [X10,X11] :
      ( sK6(X10,X11) = X10
      | ~ v1_zfmisc_1(sK6(X10,X11))
      | v1_xboole_0(X10)
      | sP0(X10,X11) ) ),
    inference(resolution,[],[f227,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK6(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f63,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f117,f149])).

fof(f149,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f148,f94])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f137,f81])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( sP3(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP3(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP3(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP3(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f25,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f137,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ v1_xboole_0(X1)
      | ~ r1_tarski(X3,X1) ) ),
    inference(resolution,[],[f91,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f117,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f114])).

fof(f114,plain,(
    ! [X4,X3] :
      ( k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_xboole_0)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f86,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( r1_tarski(k1_xboole_0,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f83,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f307,plain,(
    ! [X2,X3] :
      ( v1_zfmisc_1(sK6(X2,X3))
      | ~ l1_pre_topc(X3)
      | ~ v2_tdlat_3(X3)
      | v2_struct_0(X3)
      | sP0(X2,X3) ) ),
    inference(subsumption_resolution,[],[f306,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK6(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f306,plain,(
    ! [X2,X3] :
      ( ~ v2_tex_2(sK6(X2,X3),X3)
      | v1_zfmisc_1(sK6(X2,X3))
      | ~ l1_pre_topc(X3)
      | ~ v2_tdlat_3(X3)
      | v2_struct_0(X3)
      | sP0(X2,X3) ) ),
    inference(resolution,[],[f281,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f403,plain,
    ( spl8_17
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f174,f97,f400])).

fof(f97,plain,
    ( spl8_1
  <=> v3_tex_2(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f174,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | sP1(sK4,sK5) ),
    inference(resolution,[],[f172,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f172,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f169,f58])).

fof(f169,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f75,f60])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f29,f28,f27])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f185,plain,
    ( ~ spl8_7
    | ~ spl8_8
    | spl8_1 ),
    inference(avatar_split_clause,[],[f176,f97,f182,f178])).

fof(f176,plain,
    ( ~ sP0(sK5,sK4)
    | ~ v2_tex_2(sK5,sK4)
    | spl8_1 ),
    inference(resolution,[],[f175,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f175,plain,
    ( ~ sP1(sK4,sK5)
    | spl8_1 ),
    inference(subsumption_resolution,[],[f173,f99])).

fof(f99,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f173,plain,
    ( ~ sP1(sK4,sK5)
    | v3_tex_2(sK5,sK4) ),
    inference(resolution,[],[f172,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f61,f101,f97])).

fof(f61,plain,
    ( v1_zfmisc_1(sK5)
    | v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f104,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f62,f101,f97])).

fof(f62,plain,
    ( ~ v1_zfmisc_1(sK5)
    | ~ v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (28637)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (28629)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (28626)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (28628)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (28630)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (28645)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (28639)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (28625)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (28628)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (28638)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (28634)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (28631)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (28630)Refutation not found, incomplete strategy% (28630)------------------------------
% 0.21/0.51  % (28630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28630)Memory used [KB]: 10618
% 0.21/0.51  % (28630)Time elapsed: 0.104 s
% 0.21/0.51  % (28630)------------------------------
% 0.21/0.51  % (28630)------------------------------
% 0.21/0.51  % (28633)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (28644)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (28632)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (28646)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (28643)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (28627)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (28636)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (28625)Refutation not found, incomplete strategy% (28625)------------------------------
% 0.21/0.52  % (28625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28625)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28625)Memory used [KB]: 10746
% 0.21/0.52  % (28625)Time elapsed: 0.106 s
% 0.21/0.52  % (28625)------------------------------
% 0.21/0.52  % (28625)------------------------------
% 0.21/0.52  % (28647)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (28649)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (28648)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (28635)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f660,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f104,f105,f185,f403,f629,f647,f652,f659])).
% 0.21/0.52  fof(f659,plain,(
% 0.21/0.52    spl8_7 | ~spl8_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f657,f400,f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    spl8_7 <=> v2_tex_2(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    spl8_17 <=> sP1(sK4,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.52  fof(f657,plain,(
% 0.21/0.52    v2_tex_2(sK5,sK4) | ~spl8_17),
% 0.21/0.52    inference(resolution,[],[f402,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f402,plain,(
% 0.21/0.52    sP1(sK4,sK5) | ~spl8_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f400])).
% 0.21/0.52  fof(f652,plain,(
% 0.21/0.52    spl8_7 | ~spl8_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f651,f101,f178])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl8_2 <=> v1_zfmisc_1(sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.52  fof(f651,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f650,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ~v2_struct_0(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ((~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f34,f36,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_tdlat_3(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK4)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK4)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)) & (v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & ~v1_xboole_0(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.52  fof(f650,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f649,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    v2_tdlat_3(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f649,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f648,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    l1_pre_topc(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f648,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | ~l1_pre_topc(sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f536,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ~v1_xboole_0(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f536,plain,(
% 0.21/0.52    ~v1_zfmisc_1(sK5) | v2_tex_2(sK5,sK4) | v1_xboole_0(sK5) | ~l1_pre_topc(sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(resolution,[],[f311,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f78,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.52  fof(f647,plain,(
% 0.21/0.52    spl8_2 | ~spl8_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f646,f178,f101])).
% 0.21/0.52  fof(f646,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f645,f55])).
% 0.21/0.52  fof(f645,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f644,f57])).
% 0.21/0.52  fof(f644,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f304,f58])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    ~v2_tex_2(sK5,sK4) | v1_zfmisc_1(sK5) | ~l1_pre_topc(sK4) | ~v2_tdlat_3(sK4) | v2_struct_0(sK4)),
% 0.21/0.52    inference(resolution,[],[f281,f60])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f280,f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f64])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f629,plain,(
% 0.21/0.52    spl8_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f628])).
% 0.21/0.52  fof(f628,plain,(
% 0.21/0.52    $false | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f627,f59])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f626,f58])).
% 0.21/0.52  fof(f626,plain,(
% 0.21/0.52    ~l1_pre_topc(sK4) | v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f625,f55])).
% 0.21/0.52  fof(f625,plain,(
% 0.21/0.52    v2_struct_0(sK4) | ~l1_pre_topc(sK4) | v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(subsumption_resolution,[],[f620,f57])).
% 0.21/0.52  fof(f620,plain,(
% 0.21/0.52    ~v2_tdlat_3(sK4) | v2_struct_0(sK4) | ~l1_pre_topc(sK4) | v1_xboole_0(sK5) | spl8_8),
% 0.21/0.52    inference(resolution,[],[f604,f184])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ~sP0(sK5,sK4) | spl8_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f182])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    spl8_8 <=> sP0(sK5,sK4)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.52  fof(f604,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP0(X1,X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f599])).
% 0.21/0.52  fof(f599,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | v1_xboole_0(X1) | sP0(X1,X0)) )),
% 0.21/0.52    inference(resolution,[],[f307,f262])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    ( ! [X10,X11] : (~v1_zfmisc_1(sK6(X10,X11)) | v1_xboole_0(X10) | sP0(X10,X11)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f242,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sK6(X0,X1) != X0 | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | (sK6(X0,X1) != X0 & r1_tarski(X0,sK6(X0,X1)) & v2_tex_2(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK6(X0,X1) != X0 & r1_tarski(X0,sK6(X0,X1)) & v2_tex_2(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.52    inference(rectify,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    ( ! [X10,X11] : (sK6(X10,X11) = X10 | ~v1_zfmisc_1(sK6(X10,X11)) | v1_xboole_0(X10) | sP0(X10,X11)) )),
% 0.21/0.52    inference(resolution,[],[f227,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,sK6(X0,X1)) | sP0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f117,f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f148,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_xboole_0(X0) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(resolution,[],[f137,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ! [X0] : ((sP3(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f32,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (sP3(X1,X0) & r2_hidden(X1,X0)) => (sP3(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (sP3(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(definition_folding,[],[f25,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP3(X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~r2_hidden(X2,X3) | ~v1_xboole_0(X1) | ~r1_tarski(X3,X1)) )),
% 0.21/0.52    inference(resolution,[],[f91,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.53    inference(nnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.53    inference(condensation,[],[f114])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k1_xboole_0 = X3 | ~r1_tarski(X3,k1_xboole_0) | ~r1_tarski(X3,X4)) )),
% 0.21/0.53    inference(resolution,[],[f86,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r1_tarski(k1_xboole_0,X2) | ~r1_tarski(X2,X3)) )),
% 0.21/0.53    inference(superposition,[],[f83,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f52])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.53  fof(f307,plain,(
% 0.21/0.53    ( ! [X2,X3] : (v1_zfmisc_1(sK6(X2,X3)) | ~l1_pre_topc(X3) | ~v2_tdlat_3(X3) | v2_struct_0(X3) | sP0(X2,X3)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f306,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (v2_tex_2(sK6(X0,X1),X1) | sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f306,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~v2_tex_2(sK6(X2,X3),X3) | v1_zfmisc_1(sK6(X2,X3)) | ~l1_pre_topc(X3) | ~v2_tdlat_3(X3) | v2_struct_0(X3) | sP0(X2,X3)) )),
% 0.21/0.53    inference(resolution,[],[f281,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f45])).
% 0.21/0.53  fof(f403,plain,(
% 0.21/0.53    spl8_17 | ~spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f174,f97,f400])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl8_1 <=> v3_tex_2(sK5,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f174,plain,(
% 0.21/0.53    ~v3_tex_2(sK5,sK4) | sP1(sK4,sK5)),
% 0.21/0.53    inference(resolution,[],[f172,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.53    inference(rectify,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    sP2(sK5,sK4)),
% 0.21/0.53    inference(subsumption_resolution,[],[f169,f58])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.21/0.53    inference(resolution,[],[f75,f60])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(definition_folding,[],[f21,f29,f28,f27])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    ~spl8_7 | ~spl8_8 | spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f176,f97,f182,f178])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    ~sP0(sK5,sK4) | ~v2_tex_2(sK5,sK4) | spl8_1),
% 0.21/0.53    inference(resolution,[],[f175,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    ~sP1(sK4,sK5) | spl8_1),
% 0.21/0.53    inference(subsumption_resolution,[],[f173,f99])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~v3_tex_2(sK5,sK4) | spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f97])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    ~sP1(sK4,sK5) | v3_tex_2(sK5,sK4)),
% 0.21/0.53    inference(resolution,[],[f172,f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v3_tex_2(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    spl8_1 | spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f101,f97])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    v1_zfmisc_1(sK5) | v3_tex_2(sK5,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~spl8_1 | ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f62,f101,f97])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ~v1_zfmisc_1(sK5) | ~v3_tex_2(sK5,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f37])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (28628)------------------------------
% 0.21/0.53  % (28628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28628)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (28628)Memory used [KB]: 6396
% 0.21/0.53  % (28628)Time elapsed: 0.103 s
% 0.21/0.53  % (28628)------------------------------
% 0.21/0.53  % (28628)------------------------------
% 0.21/0.53  % (28641)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (28642)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (28623)Success in time 0.168 s
%------------------------------------------------------------------------------
