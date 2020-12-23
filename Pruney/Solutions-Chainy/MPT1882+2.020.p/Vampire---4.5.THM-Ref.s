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
% DateTime   : Thu Dec  3 13:22:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 384 expanded)
%              Number of leaves         :   22 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  522 (2679 expanded)
%              Number of equality atoms :   33 (  84 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f84,f198,f208,f210,f328,f342,f346,f351])).

fof(f351,plain,
    ( spl7_7
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f349,f195,f119])).

fof(f119,plain,
    ( spl7_7
  <=> v2_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f195,plain,
    ( spl7_10
  <=> sP1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f349,plain,
    ( v2_tex_2(sK4,sK3)
    | ~ spl7_10 ),
    inference(resolution,[],[f197,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f197,plain,
    ( sP1(sK3,sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f346,plain,
    ( spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f345,f119,f80])).

fof(f80,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f345,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4) ),
    inference(subsumption_resolution,[],[f344,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v3_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v3_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).

fof(f32,plain,
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
            | ~ v3_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK3) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK3) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK4)
        | ~ v3_tex_2(sK4,sK3) )
      & ( v1_zfmisc_1(sK4)
        | v3_tex_2(sK4,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f344,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f343,f48])).

fof(f48,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f343,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f237,f49])).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f237,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | v1_zfmisc_1(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f218,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f217,f67])).

fof(f67,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f217,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f68,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f342,plain,
    ( spl7_7
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f341,f80,f119])).

fof(f341,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f340,f46])).

fof(f340,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f339,f48])).

fof(f339,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f338,f49])).

fof(f338,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f290,f50])).

fof(f50,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f290,plain,
    ( ~ v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f216,f51])).

fof(f216,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f69,f55])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f328,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f326,f50])).

fof(f326,plain,
    ( v1_xboole_0(sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f325,f49])).

fof(f325,plain,
    ( ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f324,f46])).

fof(f324,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_8 ),
    inference(subsumption_resolution,[],[f320,f48])).

fof(f320,plain,
    ( ~ v2_tdlat_3(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | v1_xboole_0(sK4)
    | spl7_8 ),
    inference(resolution,[],[f318,f125])).

fof(f125,plain,
    ( ~ sP0(sK4,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_8
  <=> sP0(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f318,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f315])).

fof(f315,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0)
      | v1_xboole_0(X1)
      | sP0(X1,X0) ) ),
    inference(resolution,[],[f247,f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f225,f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(sK5(X0,X1))
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f233,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) != X0
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != X0
          & r1_tarski(X0,sK5(X0,X1))
          & v2_tex_2(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK5(X0,X1) != X0
        & r1_tarski(X0,sK5(X0,X1))
        & v2_tex_2(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f233,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | ~ v1_xboole_0(sK5(X0,X1))
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f133,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK5(X0,X1))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f73,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = k1_xboole_0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f88,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( ! [X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,sK6(X0)) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X2,X1) )
          & r2_hidden(X1,X0) )
     => ( ! [X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,sK6(X0)) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X2,X1) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2] :
                  ( r2_hidden(X2,X1)
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_mcart_1)).

fof(f88,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(X2,k6_subset_1(X1,X3))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f74,f72])).

fof(f72,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k6_subset_1(X1,X0)
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f224,f65])).

fof(f224,plain,(
    ! [X0,X1] :
      ( sK5(X0,X1) = X0
      | ~ v1_zfmisc_1(sK5(X0,X1))
      | v1_xboole_0(sK5(X0,X1))
      | v1_xboole_0(X0)
      | sP0(X0,X1) ) ),
    inference(resolution,[],[f54,f64])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f247,plain,(
    ! [X4,X3] :
      ( v1_zfmisc_1(sK5(X3,X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_tdlat_3(X4)
      | v2_struct_0(X4)
      | sP0(X3,X4) ) ),
    inference(subsumption_resolution,[],[f238,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f238,plain,(
    ! [X4,X3] :
      ( ~ v2_tex_2(sK5(X3,X4),X4)
      | v1_zfmisc_1(sK5(X3,X4))
      | ~ l1_pre_topc(X4)
      | ~ v2_tdlat_3(X4)
      | v2_struct_0(X4)
      | sP0(X3,X4) ) ),
    inference(resolution,[],[f218,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f210,plain,
    ( ~ spl7_7
    | ~ spl7_8
    | spl7_10 ),
    inference(avatar_split_clause,[],[f209,f195,f123,f119])).

fof(f209,plain,
    ( ~ sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | spl7_10 ),
    inference(resolution,[],[f196,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ sP0(X1,X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f196,plain,
    ( ~ sP1(sK3,sK4)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f195])).

fof(f208,plain,
    ( ~ spl7_10
    | spl7_1 ),
    inference(avatar_split_clause,[],[f115,f76,f195])).

fof(f76,plain,
    ( spl7_1
  <=> v3_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f115,plain,
    ( ~ sP1(sK3,sK4)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f113,f78])).

fof(f78,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f113,plain,
    ( ~ sP1(sK3,sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(resolution,[],[f112,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v3_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

% (2604)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f112,plain,(
    sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f109,plain,
    ( sP2(sK4,sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f19,f28,f27,f26])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f198,plain,
    ( spl7_10
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f114,f76,f195])).

fof(f114,plain,
    ( ~ v3_tex_2(sK4,sK3)
    | sP1(sK3,sK4) ),
    inference(resolution,[],[f112,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f52,f80,f76])).

fof(f52,plain,
    ( v1_zfmisc_1(sK4)
    | v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f53,f80,f76])).

fof(f53,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (2596)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (2596)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (2606)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f352,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f83,f84,f198,f208,f210,f328,f342,f346,f351])).
% 0.20/0.48  fof(f351,plain,(
% 0.20/0.48    spl7_7 | ~spl7_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f349,f195,f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    spl7_7 <=> v2_tex_2(sK4,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl7_10 <=> sP1(sK3,sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.48  fof(f349,plain,(
% 0.20/0.48    v2_tex_2(sK4,sK3) | ~spl7_10),
% 0.20/0.48    inference(resolution,[],[f197,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP1(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    sP1(sK3,sK4) | ~spl7_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f195])).
% 0.20/0.48  fof(f346,plain,(
% 0.20/0.48    spl7_2 | ~spl7_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f345,f119,f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl7_2 <=> v1_zfmisc_1(sK4)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.48  fof(f345,plain,(
% 0.20/0.48    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4)),
% 0.20/0.48    inference(subsumption_resolution,[],[f344,f46])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ~v2_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f10])).
% 0.20/0.48  fof(f10,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.20/0.48  fof(f344,plain,(
% 0.20/0.48    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | v2_struct_0(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f343,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    v2_tdlat_3(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f343,plain,(
% 0.20/0.48    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f237,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    l1_pre_topc(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f237,plain,(
% 0.20/0.48    ~v2_tex_2(sK4,sK3) | v1_zfmisc_1(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.48    inference(resolution,[],[f218,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f218,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f217,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f68,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.20/0.48  fof(f342,plain,(
% 0.20/0.48    spl7_7 | ~spl7_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f341,f80,f119])).
% 0.20/0.48  fof(f341,plain,(
% 0.20/0.48    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f340,f46])).
% 0.20/0.48  fof(f340,plain,(
% 0.20/0.48    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | v2_struct_0(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f339,f48])).
% 0.20/0.48  fof(f339,plain,(
% 0.20/0.48    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f338,f49])).
% 0.20/0.48  fof(f338,plain,(
% 0.20/0.48    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f290,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ~v1_xboole_0(sK4)),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f290,plain,(
% 0.20/0.48    ~v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | v2_struct_0(sK3)),
% 0.20/0.48    inference(resolution,[],[f216,f51])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f69,f55])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f43])).
% 0.20/0.48  fof(f328,plain,(
% 0.20/0.48    spl7_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f327])).
% 0.20/0.48  fof(f327,plain,(
% 0.20/0.48    $false | spl7_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f326,f50])).
% 0.20/0.48  fof(f326,plain,(
% 0.20/0.48    v1_xboole_0(sK4) | spl7_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f325,f49])).
% 0.20/0.48  fof(f325,plain,(
% 0.20/0.48    ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f324,f46])).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    v2_struct_0(sK3) | ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_8),
% 0.20/0.48    inference(subsumption_resolution,[],[f320,f48])).
% 0.20/0.48  fof(f320,plain,(
% 0.20/0.48    ~v2_tdlat_3(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK3) | v1_xboole_0(sK4) | spl7_8),
% 0.20/0.48    inference(resolution,[],[f318,f125])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    ~sP0(sK4,sK3) | spl7_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f123])).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl7_8 <=> sP0(sK4,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.48  fof(f318,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sP0(X1,X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f315])).
% 0.20/0.48  fof(f315,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0) | sP0(X1,X0) | v1_xboole_0(X1) | sP0(X1,X0)) )),
% 0.20/0.48    inference(resolution,[],[f247,f306])).
% 0.20/0.48  fof(f306,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f225,f234])).
% 0.20/0.48  fof(f234,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_xboole_0(sK5(X0,X1)) | sP0(X0,X1)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f233,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK5(X0,X1) != X0 | sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK5(X0,X1) != X0 & r1_tarski(X0,sK5(X0,X1)) & v2_tex_2(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.20/0.48    inference(rectify,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.20/0.48    inference(nnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK5(X0,X1) = X0 | ~v1_xboole_0(sK5(X0,X1)) | sP0(X0,X1)) )),
% 0.20/0.48    inference(resolution,[],[f133,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X0,sK5(X0,X1)) | sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | X0 = X1 | ~r1_tarski(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(superposition,[],[f73,f98])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k6_subset_1(X0,X1) = k1_xboole_0 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(resolution,[],[f88,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : ((! [X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X2,sK6(X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f23,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (! [X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X2,X1)) & r2_hidden(X1,X0)) => (! [X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X2,sK6(X0))) & r2_hidden(sK6(X0),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (! [X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X2,X1)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ~(! [X1] : ~(! [X2] : (r2_hidden(X2,X1) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_mcart_1)).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    ( ! [X2,X3,X1] : (~r2_hidden(X2,k6_subset_1(X1,X3)) | ~v1_xboole_0(X1)) )),
% 0.20/0.49    inference(resolution,[],[f74,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f224,f65])).
% 0.20/0.49  fof(f224,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sK5(X0,X1) = X0 | ~v1_zfmisc_1(sK5(X0,X1)) | v1_xboole_0(sK5(X0,X1)) | v1_xboole_0(X0) | sP0(X0,X1)) )),
% 0.20/0.49    inference(resolution,[],[f54,f64])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    ( ! [X4,X3] : (v1_zfmisc_1(sK5(X3,X4)) | ~l1_pre_topc(X4) | ~v2_tdlat_3(X4) | v2_struct_0(X4) | sP0(X3,X4)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f238,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_tex_2(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    ( ! [X4,X3] : (~v2_tex_2(sK5(X3,X4),X4) | v1_zfmisc_1(sK5(X3,X4)) | ~l1_pre_topc(X4) | ~v2_tdlat_3(X4) | v2_struct_0(X4) | sP0(X3,X4)) )),
% 0.20/0.49    inference(resolution,[],[f218,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) | sP0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f42])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~spl7_7 | ~spl7_8 | spl7_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f209,f195,f123,f119])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ~sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | spl7_10),
% 0.20/0.49    inference(resolution,[],[f196,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f38])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ~sP1(sK3,sK4) | spl7_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f195])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ~spl7_10 | spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f115,f76,f195])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl7_1 <=> v3_tex_2(sK4,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ~sP1(sK3,sK4) | spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f113,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ~v3_tex_2(sK4,sK3) | spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ~sP1(sK3,sK4) | v3_tex_2(sK4,sK3)),
% 0.20/0.49    inference(resolution,[],[f112,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v3_tex_2(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.20/0.49    inference(rectify,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.49  % (2604)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    sP2(sK4,sK3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f109,f49])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    sP2(sK4,sK3) | ~l1_pre_topc(sK3)),
% 0.20/0.49    inference(resolution,[],[f66,f51])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(definition_folding,[],[f19,f28,f27,f26])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    spl7_10 | ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f114,f76,f195])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ~v3_tex_2(sK4,sK3) | sP1(sK3,sK4)),
% 0.20/0.49    inference(resolution,[],[f112,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl7_1 | spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f52,f80,f76])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    v1_zfmisc_1(sK4) | v3_tex_2(sK4,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ~spl7_1 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f53,f80,f76])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~v1_zfmisc_1(sK4) | ~v3_tex_2(sK4,sK3)),
% 0.20/0.49    inference(cnf_transformation,[],[f34])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (2596)------------------------------
% 0.20/0.49  % (2596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (2596)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (2596)Memory used [KB]: 6268
% 0.20/0.49  % (2596)Time elapsed: 0.075 s
% 0.20/0.49  % (2596)------------------------------
% 0.20/0.49  % (2596)------------------------------
% 0.20/0.49  % (2612)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (2591)Success in time 0.132 s
%------------------------------------------------------------------------------
