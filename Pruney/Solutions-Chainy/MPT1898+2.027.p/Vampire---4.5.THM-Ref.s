%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 271 expanded)
%              Number of leaves         :   23 (  96 expanded)
%              Depth                    :   14
%              Number of atoms          :  311 ( 857 expanded)
%              Number of equality atoms :   23 (  89 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f125,f139,f448,f533])).

fof(f533,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f532])).

fof(f532,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f504,f401])).

fof(f401,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f384,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f384,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f371,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f371,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f353,f359])).

fof(f359,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f291,f241])).

fof(f241,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k4_xboole_0(X3,X3)
        | ~ sP5(X3) )
    | ~ spl6_10 ),
    inference(superposition,[],[f96,f145])).

fof(f145,plain,
    ( ! [X0] :
        ( k4_xboole_0(X0,X0) = X0
        | ~ sP5(X0) )
    | ~ spl6_10 ),
    inference(superposition,[],[f138,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ sP5(X0) ) ),
    inference(resolution,[],[f47,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f54,f57_D])).

fof(f57,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f57_D])).

fof(f57_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( sP1(sK4(X0),X0)
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP1(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP1(sK4(X0),X0)
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP1(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f17,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f138,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_10
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f96,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f49,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

% (15333)Refutation not found, incomplete strategy% (15333)------------------------------
% (15333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15333)Termination reason: Refutation not found, incomplete strategy

% (15333)Memory used [KB]: 10618
% (15333)Time elapsed: 0.070 s
% (15333)------------------------------
% (15333)------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f291,plain,
    ( ! [X0] : sP5(k4_xboole_0(k1_xboole_0,X0))
    | ~ spl6_5 ),
    inference(unit_resulting_resolution,[],[f82,f87,f57])).

fof(f87,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f49,f51])).

fof(f82,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f353,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f291,f145])).

fof(f504,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | spl6_4
    | ~ spl6_17 ),
    inference(unit_resulting_resolution,[],[f77,f72,f67,f62,f397,f447,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X0,X1)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f447,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl6_17
  <=> v2_tex_2(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f397,plain,(
    ! [X0] : ~ sP0(sK2,X0) ),
    inference(subsumption_resolution,[],[f394,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_tex_2(sK3(X0,X1),X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v3_tex_2(sK3(X0,X1),X0)
        & r1_tarski(X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_tex_2(sK3(X0,X1),X0)
        & r1_tarski(X1,sK3(X0,X1))
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( v3_tex_2(X2,X0)
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f394,plain,(
    ! [X0] :
      ( ~ sP0(sK2,X0)
      | ~ v3_tex_2(sK3(sK2,X0),sK2) ) ),
    inference(resolution,[],[f40,f38])).

fof(f38,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_tex_2(X1,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ! [X1] :
        ( ~ v3_tex_2(X1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    & l1_pre_topc(sK2)
    & v3_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ! [X1] :
            ( ~ v3_tex_2(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ! [X1] :
          ( ~ v3_tex_2(X1,sK2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v3_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f62,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_1
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f67,plain,
    ( v3_tdlat_3(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl6_2
  <=> v3_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f72,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_3
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f77,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl6_4
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f448,plain,
    ( spl6_17
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f438,f136,f80,f75,f70,f60,f445])).

fof(f438,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ spl6_1
    | ~ spl6_3
    | spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f77,f72,f62,f82,f401,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f139,plain,
    ( spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f127,f120,f136])).

fof(f120,plain,
    ( spl6_8
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f127,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f122,f53])).

fof(f122,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f125,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f124,f120])).

fof(f124,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(global_subsumption,[],[f114])).

fof(f114,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f111,f99])).

fof(f99,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_xboole_0,X4)
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f49,f53])).

fof(f111,plain,(
    ! [X0,X1] : r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f49,f99])).

fof(f83,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f39,f80])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f78,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f37,f60])).

fof(f37,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (15332)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.46  % (15331)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.46  % (15337)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.46  % (15331)Refutation not found, incomplete strategy% (15331)------------------------------
% 0.20/0.46  % (15331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15331)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (15331)Memory used [KB]: 10618
% 0.20/0.47  % (15331)Time elapsed: 0.051 s
% 0.20/0.47  % (15331)------------------------------
% 0.20/0.47  % (15331)------------------------------
% 0.20/0.47  % (15346)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.48  % (15333)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (15345)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (15346)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f537,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f63,f68,f73,f78,f83,f125,f139,f448,f533])).
% 0.20/0.48  fof(f533,plain,(
% 0.20/0.48    ~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_17),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f532])).
% 0.20/0.48  fof(f532,plain,(
% 0.20/0.48    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_17)),
% 0.20/0.48    inference(subsumption_resolution,[],[f504,f401])).
% 0.20/0.48  fof(f401,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | (~spl6_5 | ~spl6_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f384,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f384,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl6_5 | ~spl6_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f371,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.48  fof(f371,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl6_5 | ~spl6_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f353,f359])).
% 0.20/0.48  fof(f359,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ) | (~spl6_5 | ~spl6_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f291,f241])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(X3,X3) | ~sP5(X3)) ) | ~spl6_10),
% 0.20/0.48    inference(superposition,[],[f96,f145])).
% 0.20/0.48  fof(f145,plain,(
% 0.20/0.48    ( ! [X0] : (k4_xboole_0(X0,X0) = X0 | ~sP5(X0)) ) | ~spl6_10),
% 0.20/0.48    inference(superposition,[],[f138,f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~sP5(X0)) )),
% 0.20/0.48    inference(resolution,[],[f47,f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 0.20/0.48    inference(general_splitting,[],[f54,f57_D])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f57_D])).
% 0.20/0.48  fof(f57_D,plain,(
% 0.20/0.48    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 0.20/0.48    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X0] : ((sP1(sK4(X0),X0) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (sP1(X1,X0) & r2_hidden(X1,X0)) => (sP1(sK4(X0),X0) & r2_hidden(sK4(X0),X0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (sP1(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(definition_folding,[],[f17,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP1(X1,X0))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl6_10 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f49,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  % (15333)Refutation not found, incomplete strategy% (15333)------------------------------
% 0.20/0.48  % (15333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (15333)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (15333)Memory used [KB]: 10618
% 0.20/0.48  % (15333)Time elapsed: 0.070 s
% 0.20/0.48  % (15333)------------------------------
% 0.20/0.48  % (15333)------------------------------
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    ( ! [X0] : (sP5(k4_xboole_0(k1_xboole_0,X0))) ) | ~spl6_5),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f82,f87,f57])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f49,f51])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    spl6_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f353,plain,(
% 0.20/0.48    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k4_xboole_0(k1_xboole_0,X0),k4_xboole_0(k1_xboole_0,X0))) ) | (~spl6_5 | ~spl6_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f291,f145])).
% 0.20/0.48  fof(f504,plain,(
% 0.20/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | spl6_4 | ~spl6_17)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f77,f72,f67,f62,f397,f447,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (sP0(X0,X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(definition_folding,[],[f14,f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.20/0.48  fof(f447,plain,(
% 0.20/0.48    v2_tex_2(k1_xboole_0,sK2) | ~spl6_17),
% 0.20/0.48    inference(avatar_component_clause,[],[f445])).
% 0.20/0.48  fof(f445,plain,(
% 0.20/0.48    spl6_17 <=> v2_tex_2(k1_xboole_0,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.48  fof(f397,plain,(
% 0.20/0.48    ( ! [X0] : (~sP0(sK2,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f394,f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v3_tex_2(sK3(X0,X1),X0) | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : ((v3_tex_2(sK3(X0,X1),X0) & r1_tarski(X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_tex_2(sK3(X0,X1),X0) & r1_tarski(X1,sK3(X0,X1)) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1))),
% 0.20/0.48    inference(nnf_transformation,[],[f19])).
% 0.20/0.48  fof(f394,plain,(
% 0.20/0.48    ( ! [X0] : (~sP0(sK2,X0) | ~v3_tex_2(sK3(sK2,X0),sK2)) )),
% 0.20/0.48    inference(resolution,[],[f40,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_tex_2(X1,sK2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X1] : (~v3_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (! [X1] : (~v3_tex_2(X1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v3_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    l1_pre_topc(sK2) | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl6_1 <=> l1_pre_topc(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    v3_tdlat_3(sK2) | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl6_2 <=> v3_tdlat_3(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    v2_pre_topc(sK2) | ~spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl6_3 <=> v2_pre_topc(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    ~v2_struct_0(sK2) | spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    spl6_4 <=> v2_struct_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f448,plain,(
% 0.20/0.48    spl6_17 | ~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f438,f136,f80,f75,f70,f60,f445])).
% 0.20/0.48  fof(f438,plain,(
% 0.20/0.48    v2_tex_2(k1_xboole_0,sK2) | (~spl6_1 | ~spl6_3 | spl6_4 | ~spl6_5 | ~spl6_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f77,f72,f62,f82,f401,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl6_10 | ~spl6_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f127,f120,f136])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    spl6_8 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl6_8),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f122,f53])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl6_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f120])).
% 0.20/0.48  fof(f125,plain,(
% 0.20/0.48    spl6_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f124,f120])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(global_subsumption,[],[f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f111,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X4,X5] : (r1_tarski(k1_xboole_0,X4) | ~r1_tarski(X4,X5)) )),
% 0.20/0.48    inference(superposition,[],[f49,f53])).
% 0.20/0.48  fof(f111,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k1_xboole_0,k4_xboole_0(X0,X1))) )),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f49,f99])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f80])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f34,f75])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ~v2_struct_0(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f70])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v2_pre_topc(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f65])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v3_tdlat_3(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f60])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    l1_pre_topc(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (15346)------------------------------
% 0.20/0.48  % (15346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (15346)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (15346)Memory used [KB]: 10874
% 0.20/0.49  % (15346)Time elapsed: 0.072 s
% 0.20/0.49  % (15346)------------------------------
% 0.20/0.49  % (15346)------------------------------
% 0.20/0.49  % (15329)Success in time 0.133 s
%------------------------------------------------------------------------------
