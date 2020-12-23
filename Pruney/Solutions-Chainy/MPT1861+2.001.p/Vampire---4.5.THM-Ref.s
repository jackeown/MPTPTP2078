%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:51 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 238 expanded)
%              Number of leaves         :   29 (  95 expanded)
%              Depth                    :   19
%              Number of atoms          :  405 ( 852 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f625,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f77,f81,f85,f89,f110,f189,f539,f557,f562,f575,f583,f593,f612,f616])).

fof(f616,plain,(
    spl5_28 ),
    inference(avatar_contradiction_clause,[],[f613])).

fof(f613,plain,
    ( $false
    | spl5_28 ),
    inference(resolution,[],[f611,f55])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f39,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f611,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f610])).

fof(f610,plain,
    ( spl5_28
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f612,plain,
    ( ~ spl5_19
    | ~ spl5_28
    | spl5_15
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f602,f591,f187,f610,f552])).

fof(f552,plain,
    ( spl5_19
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f187,plain,
    ( spl5_15
  <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f591,plain,
    ( spl5_25
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f602,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_15
    | ~ spl5_25 ),
    inference(resolution,[],[f592,f188])).

fof(f188,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f187])).

fof(f592,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f591])).

fof(f593,plain,
    ( ~ spl5_5
    | spl5_25
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f588,f87,f72,f591,f83])).

fof(f83,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( spl5_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f87,plain,
    ( spl5_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f588,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f73,f348])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X1,sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f38,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ r1_tarski(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).

fof(f73,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f583,plain,
    ( ~ spl5_8
    | spl5_23 ),
    inference(avatar_contradiction_clause,[],[f576])).

fof(f576,plain,
    ( $false
    | ~ spl5_8
    | spl5_23 ),
    inference(resolution,[],[f574,f390])).

fof(f390,plain,
    ( ! [X7] : r1_tarski(k1_setfam_1(k2_tarski(sK1,X7)),u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(superposition,[],[f55,f371])).

fof(f371,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,X2))))
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f368,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f368,plain,
    ( ! [X2] : k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK1,X2)),u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(resolution,[],[f363,f55])).

fof(f363,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0 )
    | ~ spl5_8 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0
        | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0 )
    | ~ spl5_8 ),
    inference(resolution,[],[f358,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f358,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0 )
    | ~ spl5_8 ),
    inference(resolution,[],[f226,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f226,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK3(X4,u1_struct_0(sK0)),X5)
        | k1_setfam_1(k2_tarski(X4,u1_struct_0(sK0))) = X4
        | ~ r1_tarski(X5,sK1) )
    | ~ spl5_8 ),
    inference(resolution,[],[f214,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f214,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK3(X2,u1_struct_0(sK0)),sK1)
        | k1_setfam_1(k2_tarski(X2,u1_struct_0(sK0))) = X2 )
    | ~ spl5_8 ),
    inference(superposition,[],[f153,f109])).

fof(f109,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_8
  <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f153,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK3(X4,X5),k1_setfam_1(k2_tarski(X6,X5)))
      | k1_setfam_1(k2_tarski(X4,X5)) = X4 ) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f96,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK3(X4,X5),X5)
      | k1_setfam_1(k2_tarski(X4,X5)) = X4 ) ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f574,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | spl5_23 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl5_23
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f575,plain,
    ( ~ spl5_23
    | spl5_19 ),
    inference(avatar_split_clause,[],[f571,f552,f573])).

fof(f571,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | spl5_19 ),
    inference(resolution,[],[f553,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f553,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_19 ),
    inference(avatar_component_clause,[],[f552])).

fof(f562,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f556,f90])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0) ),
    inference(superposition,[],[f55,f40])).

fof(f556,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f555])).

fof(f555,plain,
    ( spl5_20
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f557,plain,
    ( ~ spl5_19
    | ~ spl5_20
    | spl5_15
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f541,f537,f187,f555,f552])).

fof(f537,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f541,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_15
    | ~ spl5_16 ),
    inference(resolution,[],[f538,f188])).

fof(f538,plain,
    ( ! [X0] :
        ( v2_tex_2(X0,sK0)
        | ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f537])).

fof(f539,plain,
    ( ~ spl5_4
    | spl5_16
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f535,f87,f75,f537,f79])).

fof(f79,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f75,plain,
    ( spl5_3
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f535,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f348,f76])).

fof(f76,plain,
    ( v2_tex_2(sK2,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f189,plain,
    ( ~ spl5_4
    | ~ spl5_15
    | spl5_1 ),
    inference(avatar_split_clause,[],[f184,f68,f187,f79])).

fof(f68,plain,
    ( spl5_1
  <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f184,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1 ),
    inference(superposition,[],[f69,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f48,f41])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f69,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f110,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f101,f83,f108])).

fof(f101,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(resolution,[],[f97,f84])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f97,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | k1_setfam_1(k2_tarski(X6,X7)) = X6 ) ),
    inference(resolution,[],[f56,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f87])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & ( v2_tex_2(sK2,sK0)
      | v2_tex_2(sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
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

fof(f21,plain,
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

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).

fof(f85,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f34,f83])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f77,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f36,f75,f72])).

fof(f36,plain,
    ( v2_tex_2(sK2,sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f70,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f68])).

fof(f37,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (14378)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (14389)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (14377)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (14401)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (14376)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (14395)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (14403)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (14375)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (14382)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (14397)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (14379)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (14395)Refutation not found, incomplete strategy% (14395)------------------------------
% 0.21/0.52  % (14395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (14395)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (14395)Memory used [KB]: 10746
% 0.21/0.52  % (14395)Time elapsed: 0.125 s
% 0.21/0.52  % (14395)------------------------------
% 0.21/0.52  % (14395)------------------------------
% 0.21/0.53  % (14378)Refutation not found, incomplete strategy% (14378)------------------------------
% 0.21/0.53  % (14378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14378)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14378)Memory used [KB]: 6268
% 0.21/0.53  % (14378)Time elapsed: 0.096 s
% 0.21/0.53  % (14378)------------------------------
% 0.21/0.53  % (14378)------------------------------
% 0.21/0.53  % (14383)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (14386)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (14394)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (14380)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (14386)Refutation not found, incomplete strategy% (14386)------------------------------
% 0.21/0.53  % (14386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (14386)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (14386)Memory used [KB]: 10746
% 0.21/0.53  % (14386)Time elapsed: 0.119 s
% 0.21/0.53  % (14386)------------------------------
% 0.21/0.53  % (14386)------------------------------
% 0.21/0.53  % (14390)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (14396)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (14374)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (14400)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (14402)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (14381)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (14384)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (14384)Refutation not found, incomplete strategy% (14384)------------------------------
% 0.21/0.54  % (14384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14388)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (14382)Refutation not found, incomplete strategy% (14382)------------------------------
% 0.21/0.54  % (14382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (14382)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (14382)Memory used [KB]: 10746
% 0.21/0.54  % (14382)Time elapsed: 0.137 s
% 0.21/0.54  % (14382)------------------------------
% 0.21/0.54  % (14382)------------------------------
% 0.21/0.54  % (14392)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (14404)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (14387)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (14392)Refutation not found, incomplete strategy% (14392)------------------------------
% 0.21/0.55  % (14392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14392)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14392)Memory used [KB]: 10618
% 0.21/0.55  % (14392)Time elapsed: 0.138 s
% 0.21/0.55  % (14392)------------------------------
% 0.21/0.55  % (14392)------------------------------
% 0.21/0.55  % (14397)Refutation not found, incomplete strategy% (14397)------------------------------
% 0.21/0.55  % (14397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (14397)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14397)Memory used [KB]: 10746
% 0.21/0.55  % (14397)Time elapsed: 0.144 s
% 0.21/0.55  % (14397)------------------------------
% 0.21/0.55  % (14397)------------------------------
% 0.21/0.55  % (14393)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (14391)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (14398)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (14399)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (14384)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (14384)Memory used [KB]: 10746
% 0.21/0.55  % (14384)Time elapsed: 0.140 s
% 0.21/0.55  % (14384)------------------------------
% 0.21/0.55  % (14384)------------------------------
% 1.47/0.56  % (14396)Refutation not found, incomplete strategy% (14396)------------------------------
% 1.47/0.56  % (14396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (14396)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (14396)Memory used [KB]: 1791
% 1.47/0.56  % (14396)Time elapsed: 0.131 s
% 1.47/0.56  % (14396)------------------------------
% 1.47/0.56  % (14396)------------------------------
% 1.47/0.56  % (14394)Refutation found. Thanks to Tanya!
% 1.47/0.56  % SZS status Theorem for theBenchmark
% 1.47/0.56  % SZS output start Proof for theBenchmark
% 1.47/0.56  fof(f625,plain,(
% 1.47/0.56    $false),
% 1.47/0.56    inference(avatar_sat_refutation,[],[f70,f77,f81,f85,f89,f110,f189,f539,f557,f562,f575,f583,f593,f612,f616])).
% 1.47/0.56  fof(f616,plain,(
% 1.47/0.56    spl5_28),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f613])).
% 1.47/0.56  fof(f613,plain,(
% 1.47/0.56    $false | spl5_28),
% 1.47/0.56    inference(resolution,[],[f611,f55])).
% 1.47/0.56  fof(f55,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 1.47/0.56    inference(definition_unfolding,[],[f39,f41])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f7])).
% 1.47/0.56  fof(f7,axiom,(
% 1.47/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f3])).
% 1.47/0.56  fof(f3,axiom,(
% 1.47/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.47/0.56  fof(f611,plain,(
% 1.47/0.56    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | spl5_28),
% 1.47/0.56    inference(avatar_component_clause,[],[f610])).
% 1.47/0.56  fof(f610,plain,(
% 1.47/0.56    spl5_28 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.47/0.56  fof(f612,plain,(
% 1.47/0.56    ~spl5_19 | ~spl5_28 | spl5_15 | ~spl5_25),
% 1.47/0.56    inference(avatar_split_clause,[],[f602,f591,f187,f610,f552])).
% 1.47/0.56  fof(f552,plain,(
% 1.47/0.56    spl5_19 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.47/0.56  fof(f187,plain,(
% 1.47/0.56    spl5_15 <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.47/0.56  fof(f591,plain,(
% 1.47/0.56    spl5_25 <=> ! [X0] : (~r1_tarski(X0,sK1) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.47/0.56  fof(f602,plain,(
% 1.47/0.56    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_15 | ~spl5_25)),
% 1.47/0.56    inference(resolution,[],[f592,f188])).
% 1.47/0.56  fof(f188,plain,(
% 1.47/0.56    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl5_15),
% 1.47/0.56    inference(avatar_component_clause,[],[f187])).
% 1.47/0.56  fof(f592,plain,(
% 1.47/0.56    ( ! [X0] : (v2_tex_2(X0,sK0) | ~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_25),
% 1.47/0.56    inference(avatar_component_clause,[],[f591])).
% 1.47/0.56  fof(f593,plain,(
% 1.47/0.56    ~spl5_5 | spl5_25 | ~spl5_2 | ~spl5_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f588,f87,f72,f591,f83])).
% 1.47/0.56  fof(f83,plain,(
% 1.47/0.56    spl5_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.47/0.56  fof(f72,plain,(
% 1.47/0.56    spl5_2 <=> v2_tex_2(sK1,sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.47/0.56  fof(f87,plain,(
% 1.47/0.56    spl5_6 <=> l1_pre_topc(sK0)),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.47/0.56  fof(f588,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl5_2 | ~spl5_6)),
% 1.47/0.56    inference(resolution,[],[f73,f348])).
% 1.47/0.56  fof(f348,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~v2_tex_2(X0,sK0) | ~r1_tarski(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X1,sK0)) ) | ~spl5_6),
% 1.47/0.56    inference(resolution,[],[f38,f88])).
% 1.47/0.56  fof(f88,plain,(
% 1.47/0.56    l1_pre_topc(sK0) | ~spl5_6),
% 1.47/0.56    inference(avatar_component_clause,[],[f87])).
% 1.47/0.56  fof(f38,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X2,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f15])).
% 1.47/0.56  fof(f15,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.56    inference(flattening,[],[f14])).
% 1.47/0.56  fof(f14,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f9])).
% 1.47/0.56  fof(f9,axiom,(
% 1.47/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tex_2)).
% 1.47/0.56  fof(f73,plain,(
% 1.47/0.56    v2_tex_2(sK1,sK0) | ~spl5_2),
% 1.47/0.56    inference(avatar_component_clause,[],[f72])).
% 1.47/0.56  fof(f583,plain,(
% 1.47/0.56    ~spl5_8 | spl5_23),
% 1.47/0.56    inference(avatar_contradiction_clause,[],[f576])).
% 1.47/0.56  fof(f576,plain,(
% 1.47/0.56    $false | (~spl5_8 | spl5_23)),
% 1.47/0.56    inference(resolution,[],[f574,f390])).
% 1.47/0.56  fof(f390,plain,(
% 1.47/0.56    ( ! [X7] : (r1_tarski(k1_setfam_1(k2_tarski(sK1,X7)),u1_struct_0(sK0))) ) | ~spl5_8),
% 1.47/0.56    inference(superposition,[],[f55,f371])).
% 1.47/0.56  fof(f371,plain,(
% 1.47/0.56    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,X2))))) ) | ~spl5_8),
% 1.47/0.56    inference(forward_demodulation,[],[f368,f40])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f5])).
% 1.47/0.56  fof(f5,axiom,(
% 1.47/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.47/0.56  fof(f368,plain,(
% 1.47/0.56    ( ! [X2] : (k1_setfam_1(k2_tarski(sK1,X2)) = k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(sK1,X2)),u1_struct_0(sK0)))) ) | ~spl5_8),
% 1.47/0.56    inference(resolution,[],[f363,f55])).
% 1.47/0.56  fof(f363,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0) ) | ~spl5_8),
% 1.47/0.56    inference(duplicate_literal_removal,[],[f362])).
% 1.47/0.56  fof(f362,plain,(
% 1.47/0.56    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0 | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0) ) | ~spl5_8),
% 1.47/0.56    inference(resolution,[],[f358,f56])).
% 1.47/0.56  fof(f56,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.47/0.56    inference(definition_unfolding,[],[f42,f41])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f16])).
% 1.47/0.56  fof(f16,plain,(
% 1.47/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.47/0.56    inference(ennf_transformation,[],[f4])).
% 1.47/0.56  fof(f4,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.47/0.56  fof(f358,plain,(
% 1.47/0.56    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | k1_setfam_1(k2_tarski(X0,u1_struct_0(sK0))) = X0) ) | ~spl5_8),
% 1.47/0.56    inference(resolution,[],[f226,f44])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f26,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f24,f25])).
% 1.47/0.56  fof(f25,plain,(
% 1.47/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f24,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(rectify,[],[f23])).
% 1.47/0.56  fof(f23,plain,(
% 1.47/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.47/0.56    inference(nnf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,plain,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.47/0.56    inference(ennf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.47/0.56  fof(f226,plain,(
% 1.47/0.56    ( ! [X4,X5] : (~r2_hidden(sK3(X4,u1_struct_0(sK0)),X5) | k1_setfam_1(k2_tarski(X4,u1_struct_0(sK0))) = X4 | ~r1_tarski(X5,sK1)) ) | ~spl5_8),
% 1.47/0.56    inference(resolution,[],[f214,f43])).
% 1.47/0.56  fof(f43,plain,(
% 1.47/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f26])).
% 1.47/0.56  fof(f214,plain,(
% 1.47/0.56    ( ! [X2] : (~r2_hidden(sK3(X2,u1_struct_0(sK0)),sK1) | k1_setfam_1(k2_tarski(X2,u1_struct_0(sK0))) = X2) ) | ~spl5_8),
% 1.47/0.56    inference(superposition,[],[f153,f109])).
% 1.47/0.56  fof(f109,plain,(
% 1.47/0.56    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl5_8),
% 1.47/0.56    inference(avatar_component_clause,[],[f108])).
% 1.47/0.56  fof(f108,plain,(
% 1.47/0.56    spl5_8 <=> sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.47/0.56  fof(f153,plain,(
% 1.47/0.56    ( ! [X6,X4,X5] : (~r2_hidden(sK3(X4,X5),k1_setfam_1(k2_tarski(X6,X5))) | k1_setfam_1(k2_tarski(X4,X5)) = X4) )),
% 1.47/0.56    inference(resolution,[],[f96,f65])).
% 1.47/0.56  fof(f65,plain,(
% 1.47/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 1.47/0.56    inference(equality_resolution,[],[f62])).
% 1.47/0.56  fof(f62,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.47/0.56    inference(definition_unfolding,[],[f50,f41])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.47/0.56    inference(cnf_transformation,[],[f32])).
% 1.47/0.56  fof(f32,plain,(
% 1.47/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f30,f31])).
% 1.67/0.58  fof(f31,plain,(
% 1.67/0.58    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f30,plain,(
% 1.67/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.67/0.58    inference(rectify,[],[f29])).
% 1.67/0.58  fof(f29,plain,(
% 1.67/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.67/0.58    inference(flattening,[],[f28])).
% 1.67/0.58  fof(f28,plain,(
% 1.67/0.58    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 1.67/0.58    inference(nnf_transformation,[],[f2])).
% 1.67/0.58  fof(f2,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.67/0.58  fof(f96,plain,(
% 1.67/0.58    ( ! [X4,X5] : (~r2_hidden(sK3(X4,X5),X5) | k1_setfam_1(k2_tarski(X4,X5)) = X4) )),
% 1.67/0.58    inference(resolution,[],[f56,f45])).
% 1.67/0.58  fof(f45,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f26])).
% 1.67/0.58  fof(f574,plain,(
% 1.67/0.58    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | spl5_23),
% 1.67/0.58    inference(avatar_component_clause,[],[f573])).
% 1.67/0.58  fof(f573,plain,(
% 1.67/0.58    spl5_23 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.67/0.58  fof(f575,plain,(
% 1.67/0.58    ~spl5_23 | spl5_19),
% 1.67/0.58    inference(avatar_split_clause,[],[f571,f552,f573])).
% 1.67/0.58  fof(f571,plain,(
% 1.67/0.58    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),u1_struct_0(sK0)) | spl5_19),
% 1.67/0.58    inference(resolution,[],[f553,f47])).
% 1.67/0.58  fof(f47,plain,(
% 1.67/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.67/0.58    inference(cnf_transformation,[],[f27])).
% 1.67/0.58  fof(f27,plain,(
% 1.67/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.67/0.58    inference(nnf_transformation,[],[f8])).
% 1.67/0.58  fof(f8,axiom,(
% 1.67/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.67/0.58  fof(f553,plain,(
% 1.67/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_19),
% 1.67/0.58    inference(avatar_component_clause,[],[f552])).
% 1.67/0.58  fof(f562,plain,(
% 1.67/0.58    spl5_20),
% 1.67/0.58    inference(avatar_contradiction_clause,[],[f558])).
% 1.67/0.58  fof(f558,plain,(
% 1.67/0.58    $false | spl5_20),
% 1.67/0.58    inference(resolution,[],[f556,f90])).
% 1.67/0.58  fof(f90,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X0)),X0)) )),
% 1.67/0.58    inference(superposition,[],[f55,f40])).
% 1.67/0.58  fof(f556,plain,(
% 1.67/0.58    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | spl5_20),
% 1.67/0.58    inference(avatar_component_clause,[],[f555])).
% 1.67/0.58  fof(f555,plain,(
% 1.67/0.58    spl5_20 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.67/0.58  fof(f557,plain,(
% 1.67/0.58    ~spl5_19 | ~spl5_20 | spl5_15 | ~spl5_16),
% 1.67/0.58    inference(avatar_split_clause,[],[f541,f537,f187,f555,f552])).
% 1.67/0.58  fof(f537,plain,(
% 1.67/0.58    spl5_16 <=> ! [X0] : (~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.67/0.58  fof(f541,plain,(
% 1.67/0.58    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_15 | ~spl5_16)),
% 1.67/0.58    inference(resolution,[],[f538,f188])).
% 1.67/0.58  fof(f538,plain,(
% 1.67/0.58    ( ! [X0] : (v2_tex_2(X0,sK0) | ~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_16),
% 1.67/0.58    inference(avatar_component_clause,[],[f537])).
% 1.67/0.58  fof(f539,plain,(
% 1.67/0.58    ~spl5_4 | spl5_16 | ~spl5_3 | ~spl5_6),
% 1.67/0.58    inference(avatar_split_clause,[],[f535,f87,f75,f537,f79])).
% 1.67/0.58  fof(f79,plain,(
% 1.67/0.58    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.67/0.58  fof(f75,plain,(
% 1.67/0.58    spl5_3 <=> v2_tex_2(sK2,sK0)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.67/0.58  fof(f535,plain,(
% 1.67/0.58    ( ! [X0] : (~r1_tarski(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (~spl5_3 | ~spl5_6)),
% 1.67/0.58    inference(resolution,[],[f348,f76])).
% 1.67/0.58  fof(f76,plain,(
% 1.67/0.58    v2_tex_2(sK2,sK0) | ~spl5_3),
% 1.67/0.58    inference(avatar_component_clause,[],[f75])).
% 1.67/0.58  fof(f189,plain,(
% 1.67/0.58    ~spl5_4 | ~spl5_15 | spl5_1),
% 1.67/0.58    inference(avatar_split_clause,[],[f184,f68,f187,f79])).
% 1.67/0.58  fof(f68,plain,(
% 1.67/0.58    spl5_1 <=> v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.67/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.67/0.58  fof(f184,plain,(
% 1.67/0.58    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_1),
% 1.67/0.58    inference(superposition,[],[f69,f57])).
% 1.67/0.58  fof(f57,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.67/0.58    inference(definition_unfolding,[],[f48,f41])).
% 1.67/0.58  fof(f48,plain,(
% 1.67/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f18])).
% 1.67/0.58  fof(f18,plain,(
% 1.67/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.67/0.58    inference(ennf_transformation,[],[f6])).
% 1.67/0.58  fof(f6,axiom,(
% 1.67/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.67/0.58  fof(f69,plain,(
% 1.67/0.58    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl5_1),
% 1.67/0.58    inference(avatar_component_clause,[],[f68])).
% 1.67/0.58  fof(f110,plain,(
% 1.67/0.58    spl5_8 | ~spl5_5),
% 1.67/0.58    inference(avatar_split_clause,[],[f101,f83,f108])).
% 1.67/0.58  fof(f101,plain,(
% 1.67/0.58    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) | ~spl5_5),
% 1.67/0.58    inference(resolution,[],[f97,f84])).
% 1.67/0.58  fof(f84,plain,(
% 1.67/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 1.67/0.58    inference(avatar_component_clause,[],[f83])).
% 1.67/0.58  fof(f97,plain,(
% 1.67/0.58    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(X7)) | k1_setfam_1(k2_tarski(X6,X7)) = X6) )),
% 1.67/0.58    inference(resolution,[],[f56,f46])).
% 1.67/0.58  fof(f46,plain,(
% 1.67/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.67/0.58    inference(cnf_transformation,[],[f27])).
% 1.67/0.58  fof(f89,plain,(
% 1.67/0.58    spl5_6),
% 1.67/0.58    inference(avatar_split_clause,[],[f33,f87])).
% 1.67/0.58  fof(f33,plain,(
% 1.67/0.58    l1_pre_topc(sK0)),
% 1.67/0.58    inference(cnf_transformation,[],[f22])).
% 1.67/0.58  fof(f22,plain,(
% 1.67/0.58    ((~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.67/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f21,f20,f19])).
% 1.67/0.58  fof(f19,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f20,plain,(
% 1.67/0.58    ? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(X1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f21,plain,(
% 1.67/0.58    ? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & (v2_tex_2(X2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & (v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.67/0.58    introduced(choice_axiom,[])).
% 1.67/0.58  fof(f13,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/0.58    inference(flattening,[],[f12])).
% 1.67/0.58  fof(f12,plain,(
% 1.67/0.58    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.67/0.58    inference(ennf_transformation,[],[f11])).
% 1.67/0.58  fof(f11,negated_conjecture,(
% 1.67/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.67/0.58    inference(negated_conjecture,[],[f10])).
% 1.67/0.58  fof(f10,conjecture,(
% 1.67/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.67/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tex_2)).
% 1.67/0.58  fof(f85,plain,(
% 1.67/0.58    spl5_5),
% 1.67/0.58    inference(avatar_split_clause,[],[f34,f83])).
% 1.67/0.58  fof(f34,plain,(
% 1.67/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.58    inference(cnf_transformation,[],[f22])).
% 1.67/0.58  fof(f81,plain,(
% 1.67/0.58    spl5_4),
% 1.67/0.58    inference(avatar_split_clause,[],[f35,f79])).
% 1.67/0.59  fof(f35,plain,(
% 1.67/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  fof(f77,plain,(
% 1.67/0.59    spl5_2 | spl5_3),
% 1.67/0.59    inference(avatar_split_clause,[],[f36,f75,f72])).
% 1.67/0.59  fof(f36,plain,(
% 1.67/0.59    v2_tex_2(sK2,sK0) | v2_tex_2(sK1,sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  fof(f70,plain,(
% 1.67/0.59    ~spl5_1),
% 1.67/0.59    inference(avatar_split_clause,[],[f37,f68])).
% 1.67/0.59  fof(f37,plain,(
% 1.67/0.59    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.67/0.59    inference(cnf_transformation,[],[f22])).
% 1.67/0.59  % SZS output end Proof for theBenchmark
% 1.67/0.59  % (14394)------------------------------
% 1.67/0.59  % (14394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.59  % (14394)Termination reason: Refutation
% 1.67/0.59  
% 1.67/0.59  % (14394)Memory used [KB]: 11129
% 1.67/0.59  % (14394)Time elapsed: 0.144 s
% 1.67/0.59  % (14394)------------------------------
% 1.67/0.59  % (14394)------------------------------
% 1.67/0.59  % (14370)Success in time 0.223 s
%------------------------------------------------------------------------------
