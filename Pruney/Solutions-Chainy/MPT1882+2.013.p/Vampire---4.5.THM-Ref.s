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
% DateTime   : Thu Dec  3 13:22:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 489 expanded)
%              Number of leaves         :   22 ( 147 expanded)
%              Depth                    :   15
%              Number of atoms          :  610 (3765 expanded)
%              Number of equality atoms :   39 (  93 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f404,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f75,f99,f106,f113,f131,f137,f143,f173,f217,f381,f387,f403])).

fof(f403,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f401,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f401,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f400,f43])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f400,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f399,f87])).

fof(f87,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f399,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f396,f69])).

fof(f69,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_1
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f396,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_9 ),
    inference(trivial_inequality_removal,[],[f395])).

fof(f395,plain,
    ( sK1 != sK1
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_9 ),
    inference(superposition,[],[f53,f162])).

fof(f162,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl3_9
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f53,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
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

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

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
    inference(nnf_transformation,[],[f19])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f387,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f385,f110,f160,f156])).

fof(f156,plain,
    ( spl3_8
  <=> r1_tarski(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f110,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f385,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f112,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f112,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f381,plain,
    ( ~ spl3_7
    | spl3_8
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f380])).

fof(f380,plain,
    ( $false
    | ~ spl3_7
    | spl3_8
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f373,f228])).

fof(f228,plain,
    ( r1_tarski(k1_xboole_0,sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f58,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2(sK0,sK1))
    | ~ spl3_7 ),
    inference(resolution,[],[f112,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f373,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | spl3_8
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f158,f223])).

fof(f223,plain,
    ( k1_xboole_0 = sK2(sK0,sK1)
    | ~ spl3_10 ),
    inference(resolution,[],[f168,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f168,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_10
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f158,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f217,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f215,f172])).

fof(f172,plain,
    ( ~ v1_zfmisc_1(sK2(sK0,sK1))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_11
  <=> v1_zfmisc_1(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f215,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(resolution,[],[f213,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f213,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f212,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f212,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f211,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f211,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f210,f40])).

fof(f40,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f210,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f209,f41])).

fof(f209,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_6
    | spl3_11 ),
    inference(subsumption_resolution,[],[f208,f172])).

fof(f208,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f179,f105])).

fof(f105,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_6
  <=> v2_tex_2(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f179,plain,
    ( ~ v2_tex_2(sK2(sK0,sK1),sK0)
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f98,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f98,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_5
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f173,plain,
    ( spl3_10
    | ~ spl3_11
    | spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f164,f110,f160,f170,f166])).

fof(f164,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f154,f42])).

fof(f42,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f112,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f143,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f142,f71,f86])).

fof(f71,plain,
    ( spl3_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f142,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f38])).

fof(f141,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f140,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f139,f40])).

fof(f139,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f138,f41])).

fof(f138,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f83,f42])).

fof(f83,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f137,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f136,f86,f71])).

fof(f136,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f135,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f39])).

fof(f134,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f40])).

fof(f133,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f132,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f82,f42])).

fof(f82,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f56])).

fof(f131,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(subsumption_resolution,[],[f123,f68])).

fof(f68,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f123,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f122,f41])).

fof(f122,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f77,f88])).

fof(f88,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f77,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,
    ( ~ spl3_3
    | spl3_7
    | spl3_1 ),
    inference(avatar_split_clause,[],[f108,f67,f110,f86])).

fof(f108,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f107,f41])).

fof(f107,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f81,f69])).

fof(f81,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f106,plain,
    ( ~ spl3_3
    | spl3_6
    | spl3_1 ),
    inference(avatar_split_clause,[],[f101,f67,f103,f86])).

fof(f101,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f100,f41])).

fof(f100,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f80,f69])).

fof(f80,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,
    ( ~ spl3_3
    | spl3_5
    | spl3_1 ),
    inference(avatar_split_clause,[],[f94,f67,f96,f86])).

fof(f94,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f93,f41])).

fof(f93,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f79,f69])).

fof(f79,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f44,f71,f67])).

fof(f44,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f71,f67])).

fof(f45,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (21502)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.44  % (21493)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (21493)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f404,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f74,f75,f99,f106,f113,f131,f137,f143,f173,f217,f381,f387,f403])).
% 0.21/0.47  fof(f403,plain,(
% 0.21/0.47    spl3_1 | ~spl3_3 | ~spl3_9),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f402])).
% 0.21/0.47  fof(f402,plain,(
% 0.21/0.47    $false | (spl3_1 | ~spl3_3 | ~spl3_9)),
% 0.21/0.47    inference(subsumption_resolution,[],[f401,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.48  fof(f401,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | (spl3_1 | ~spl3_3 | ~spl3_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f400,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f400,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_1 | ~spl3_3 | ~spl3_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f399,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl3_3 <=> v2_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_1 | ~spl3_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f396,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~v3_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl3_1 <=> v3_tex_2(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_9),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f395])).
% 0.21/0.48  fof(f395,plain,(
% 0.21/0.48    sK1 != sK1 | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_9),
% 0.21/0.48    inference(superposition,[],[f53,f162])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    sK1 = sK2(sK0,sK1) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f160])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl3_9 <=> sK1 = sK2(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sK2(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.48  fof(f387,plain,(
% 0.21/0.48    ~spl3_8 | spl3_9 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f385,f110,f160,f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl3_8 <=> r1_tarski(sK2(sK0,sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl3_7 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f385,plain,(
% 0.21/0.48    sK1 = sK2(sK0,sK1) | ~r1_tarski(sK2(sK0,sK1),sK1) | ~spl3_7),
% 0.21/0.48    inference(resolution,[],[f112,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(flattening,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    ~spl3_7 | spl3_8 | ~spl3_10),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f380])).
% 0.21/0.48  fof(f380,plain,(
% 0.21/0.48    $false | (~spl3_7 | spl3_8 | ~spl3_10)),
% 0.21/0.48    inference(subsumption_resolution,[],[f373,f228])).
% 0.21/0.48  fof(f228,plain,(
% 0.21/0.48    r1_tarski(k1_xboole_0,sK1) | ~spl3_7),
% 0.21/0.48    inference(superposition,[],[f58,f152])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK1,sK2(sK0,sK1)) | ~spl3_7),
% 0.21/0.48    inference(resolution,[],[f112,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK1) | (spl3_8 | ~spl3_10)),
% 0.21/0.48    inference(backward_demodulation,[],[f158,f223])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    k1_xboole_0 = sK2(sK0,sK1) | ~spl3_10),
% 0.21/0.48    inference(resolution,[],[f168,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0,sK1)) | ~spl3_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f166])).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl3_10 <=> v1_xboole_0(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.48  fof(f158,plain,(
% 0.21/0.48    ~r1_tarski(sK2(sK0,sK1),sK1) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f156])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    ~spl3_5 | ~spl3_6 | spl3_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    $false | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f215,f172])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK2(sK0,sK1)) | spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f170])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    spl3_11 <=> v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    v1_zfmisc_1(sK2(sK0,sK1)) | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(resolution,[],[f213,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0,sK1)) | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f212,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0,sK1)) | v2_struct_0(sK0) | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f211,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f210,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v2_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f210,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0,sK1)) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f209,f41])).
% 0.21/0.48  fof(f209,plain,(
% 0.21/0.48    v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_5 | ~spl3_6 | spl3_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f208,f172])).
% 0.21/0.48  fof(f208,plain,(
% 0.21/0.48    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl3_5 | ~spl3_6)),
% 0.21/0.48    inference(subsumption_resolution,[],[f179,f105])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v2_tex_2(sK2(sK0,sK1),sK0) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl3_6 <=> v2_tex_2(sK2(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ~v2_tex_2(sK2(sK0,sK1),sK0) | v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl3_5),
% 0.21/0.48    inference(resolution,[],[f98,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_5 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl3_10 | ~spl3_11 | spl3_9 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f164,f110,f160,f170,f166])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | ~spl3_7),
% 0.21/0.48    inference(subsumption_resolution,[],[f154,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    sK1 = sK2(sK0,sK1) | ~v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1) | ~spl3_7),
% 0.21/0.48    inference(resolution,[],[f112,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl3_3 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f142,f71,f86])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl3_2 <=> v1_zfmisc_1(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f141,f38])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f140,f39])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f139,f40])).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f138,f41])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f42])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl3_2 | ~spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f136,f86,f71])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.21/0.48    inference(subsumption_resolution,[],[f135,f38])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f134,f39])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f133,f40])).
% 0.21/0.48  fof(f133,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f132,f41])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f42])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f56])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    ~spl3_1 | spl3_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    $false | (~spl3_1 | spl3_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    v3_tex_2(sK1,sK0) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~v3_tex_2(sK1,sK0) | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f41])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f77,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    ~v3_tex_2(sK1,sK0) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~spl3_3 | spl3_7 | spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f108,f67,f110,f86])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f107,f41])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f69])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~spl3_3 | spl3_6 | spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f101,f67,f103,f86])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f41])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f69])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v2_tex_2(sK2(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~spl3_3 | spl3_5 | spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f67,f96,f86])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f41])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | spl3_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f69])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.48    inference(resolution,[],[f43,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_1 | spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f71,f67])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ~spl3_1 | ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f45,f71,f67])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21493)------------------------------
% 0.21/0.48  % (21493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21493)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21493)Memory used [KB]: 10746
% 0.21/0.48  % (21493)Time elapsed: 0.082 s
% 0.21/0.48  % (21493)------------------------------
% 0.21/0.48  % (21493)------------------------------
% 0.21/0.48  % (21489)Success in time 0.12 s
%------------------------------------------------------------------------------
