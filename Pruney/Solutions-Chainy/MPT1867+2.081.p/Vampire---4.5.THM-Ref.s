%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 202 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  355 ( 731 expanded)
%              Number of equality atoms :   48 (  85 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f475,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f106,f166,f294,f296,f298,f302,f312,f407,f474])).

fof(f474,plain,
    ( ~ spl8_3
    | spl8_9
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f471,f404,f287,f309,f155])).

fof(f155,plain,
    ( spl8_3
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f309,plain,
    ( spl8_9
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f287,plain,
    ( spl8_7
  <=> m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f404,plain,
    ( spl8_14
  <=> ! [X1] : k3_xboole_0(X1,sK6(sK2)) = k9_subset_1(u1_struct_0(sK2),sK6(sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f471,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK6(sK2))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(superposition,[],[f129,f458])).

fof(f458,plain,
    ( k3_xboole_0(k1_xboole_0,sK6(sK2)) = k3_xboole_0(sK6(sK2),k1_xboole_0)
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(resolution,[],[f421,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f421,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        | k3_xboole_0(X1,sK6(sK2)) = k3_xboole_0(sK6(sK2),X1) )
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f393,f418])).

fof(f418,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK6(sK2)) = k3_xboole_0(X0,sK6(sK2))
    | ~ spl8_7
    | ~ spl8_14 ),
    inference(backward_demodulation,[],[f304,f405])).

fof(f405,plain,
    ( ! [X1] : k3_xboole_0(X1,sK6(sK2)) = k9_subset_1(u1_struct_0(sK2),sK6(sK2),X1)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f404])).

fof(f304,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK2),X0,sK6(sK2)) = k9_subset_1(u1_struct_0(sK2),sK6(sK2),X0)
    | ~ spl8_7 ),
    inference(resolution,[],[f288,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f288,plain,
    ( m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f287])).

fof(f393,plain,
    ( ! [X1] :
        ( k9_subset_1(u1_struct_0(sK2),X1,sK6(sK2)) = k3_xboole_0(sK6(sK2),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_7 ),
    inference(superposition,[],[f304,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f73,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_subset_1(k1_xboole_0,X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f112,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f72,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f407,plain,
    ( ~ spl8_7
    | spl8_14
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f394,f287,f404,f287])).

fof(f394,plain,
    ( ! [X0] :
        ( k9_subset_1(u1_struct_0(sK2),sK6(sK2),X0) = k3_xboole_0(X0,sK6(sK2))
        | ~ m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_7 ),
    inference(superposition,[],[f73,f304])).

fof(f312,plain,
    ( ~ spl8_7
    | ~ spl8_9
    | spl8_8 ),
    inference(avatar_split_clause,[],[f307,f291,f309,f287])).

fof(f291,plain,
    ( spl8_8
  <=> k1_xboole_0 = k9_subset_1(u1_struct_0(sK2),k1_xboole_0,sK6(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f307,plain,
    ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK6(sK2))
    | ~ m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_8 ),
    inference(superposition,[],[f293,f73])).

fof(f293,plain,
    ( k1_xboole_0 != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,sK6(sK2))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f291])).

fof(f302,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(avatar_split_clause,[],[f299,f287,f283,f279])).

fof(f279,plain,
    ( spl8_5
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f283,plain,
    ( spl8_6
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f299,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl8_7 ),
    inference(resolution,[],[f289,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v3_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v3_pre_topc(sK6(X0),X0)
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_tops_1)).

fof(f289,plain,
    ( ~ m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_7 ),
    inference(avatar_component_clause,[],[f287])).

fof(f298,plain,(
    spl8_6 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl8_6 ),
    inference(resolution,[],[f285,f49])).

fof(f49,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK3,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
      & v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f285,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f283])).

fof(f296,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl8_5 ),
    inference(resolution,[],[f281,f48])).

fof(f48,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f281,plain,
    ( ~ v2_pre_topc(sK2)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f279])).

fof(f294,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_7
    | ~ spl8_8
    | spl8_2 ),
    inference(avatar_split_clause,[],[f276,f98,f291,f287,f283,f279])).

fof(f98,plain,
    ( spl8_2
  <=> sP0(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f276,plain,
    ( k1_xboole_0 != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,sK6(sK2))
    | ~ m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl8_2 ),
    inference(resolution,[],[f275,f66])).

fof(f66,plain,(
    ! [X0] :
      ( v3_pre_topc(sK6(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK2)
        | k1_xboole_0 != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl8_2 ),
    inference(forward_demodulation,[],[f274,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,sK2)
    | spl8_2 ),
    inference(resolution,[],[f103,f64])).

fof(f103,plain,
    ( r1_tarski(sK4(k1_xboole_0,sK2),k1_xboole_0)
    | spl8_2 ),
    inference(resolution,[],[f100,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | r1_tarski(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(sK4(X0,X1),X0)
          & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
              & v3_pre_topc(sK5(X0,X1,X4),X1)
              & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
              | ~ v3_pre_topc(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
            | ~ v3_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
          & v3_pre_topc(X5,X1)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4
        & v3_pre_topc(sK5(X0,X1,X4),X1)
        & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X0,X3) != X2
                | ~ v3_pre_topc(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & r1_tarski(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X4] :
            ( ? [X5] :
                ( k9_subset_1(u1_struct_0(X1),X0,X5) = X4
                & v3_pre_topc(X5,X1)
                & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ r1_tarski(X4,X0)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( ? [X3] :
                ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( ? [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
              & v3_pre_topc(X3,X0)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f100,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f274,plain,
    ( ! [X0] :
        ( sK4(k1_xboole_0,sK2) != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0)
        | ~ v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | spl8_2 ),
    inference(resolution,[],[f62,f100])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( sP0(X0,X1)
      | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1)
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f166,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | spl8_3 ),
    inference(resolution,[],[f157,f53])).

fof(f157,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f155])).

fof(f106,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl8_1 ),
    inference(resolution,[],[f96,f53])).

fof(f96,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl8_1
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f101,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f92,f98,f94])).

fof(f92,plain,
    ( ~ sP0(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(resolution,[],[f90,f79])).

fof(f79,plain,(
    ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f52,f76])).

fof(f76,plain,(
    k1_xboole_0 = sK3 ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f52,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X0] :
      ( v2_tex_2(X0,sK2)
      | ~ sP0(X0,sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f88,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X1,X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_tex_2(X1,X0)
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,(
    ! [X0] :
      ( sP1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f63,f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f18,f29,f28])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (32410)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (32402)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (32394)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (32399)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (32389)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32390)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (32388)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (32393)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32391)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (32396)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (32403)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (32398)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (32387)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (32397)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (32406)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (32389)Refutation not found, incomplete strategy% (32389)------------------------------
% 0.21/0.55  % (32389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32389)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32389)Memory used [KB]: 10746
% 0.21/0.55  % (32389)Time elapsed: 0.140 s
% 0.21/0.55  % (32389)------------------------------
% 0.21/0.55  % (32389)------------------------------
% 0.21/0.55  % (32404)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (32399)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (32409)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f475,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f101,f106,f166,f294,f296,f298,f302,f312,f407,f474])).
% 0.21/0.55  fof(f474,plain,(
% 0.21/0.55    ~spl8_3 | spl8_9 | ~spl8_7 | ~spl8_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f471,f404,f287,f309,f155])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    spl8_3 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    spl8_9 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK6(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    spl8_7 <=> m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.55  fof(f404,plain,(
% 0.21/0.55    spl8_14 <=> ! [X1] : k3_xboole_0(X1,sK6(sK2)) = k9_subset_1(u1_struct_0(sK2),sK6(sK2),X1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.21/0.55  fof(f471,plain,(
% 0.21/0.55    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK6(sK2)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl8_7 | ~spl8_14)),
% 0.21/0.55    inference(superposition,[],[f129,f458])).
% 0.21/0.55  fof(f458,plain,(
% 0.21/0.55    k3_xboole_0(k1_xboole_0,sK6(sK2)) = k3_xboole_0(sK6(sK2),k1_xboole_0) | (~spl8_7 | ~spl8_14)),
% 0.21/0.55    inference(resolution,[],[f421,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.55  fof(f421,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | k3_xboole_0(X1,sK6(sK2)) = k3_xboole_0(sK6(sK2),X1)) ) | (~spl8_7 | ~spl8_14)),
% 0.21/0.55    inference(backward_demodulation,[],[f393,f418])).
% 0.21/0.55  fof(f418,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),X0,sK6(sK2)) = k3_xboole_0(X0,sK6(sK2))) ) | (~spl8_7 | ~spl8_14)),
% 0.21/0.55    inference(backward_demodulation,[],[f304,f405])).
% 0.21/0.55  fof(f405,plain,(
% 0.21/0.55    ( ! [X1] : (k3_xboole_0(X1,sK6(sK2)) = k9_subset_1(u1_struct_0(sK2),sK6(sK2),X1)) ) | ~spl8_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f404])).
% 0.21/0.55  fof(f304,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),X0,sK6(sK2)) = k9_subset_1(u1_struct_0(sK2),sK6(sK2),X0)) ) | ~spl8_7),
% 0.21/0.55    inference(resolution,[],[f288,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.55  fof(f288,plain,(
% 0.21/0.55    m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f287])).
% 0.21/0.55  fof(f393,plain,(
% 0.21/0.55    ( ! [X1] : (k9_subset_1(u1_struct_0(sK2),X1,sK6(sK2)) = k3_xboole_0(sK6(sK2),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_7),
% 0.21/0.55    inference(superposition,[],[f304,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.55    inference(superposition,[],[f73,f113])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_xboole_0 = k9_subset_1(k1_xboole_0,X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.55    inference(resolution,[],[f112,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.55    inference(resolution,[],[f72,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    ~spl8_7 | spl8_14 | ~spl8_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f394,f287,f404,f287])).
% 0.21/0.55  fof(f394,plain,(
% 0.21/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK2),sK6(sK2),X0) = k3_xboole_0(X0,sK6(sK2)) | ~m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_7),
% 0.21/0.55    inference(superposition,[],[f73,f304])).
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    ~spl8_7 | ~spl8_9 | spl8_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f307,f291,f309,f287])).
% 0.21/0.55  fof(f291,plain,(
% 0.21/0.55    spl8_8 <=> k1_xboole_0 = k9_subset_1(u1_struct_0(sK2),k1_xboole_0,sK6(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    k1_xboole_0 != k3_xboole_0(k1_xboole_0,sK6(sK2)) | ~m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | spl8_8),
% 0.21/0.55    inference(superposition,[],[f293,f73])).
% 0.21/0.55  fof(f293,plain,(
% 0.21/0.55    k1_xboole_0 != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,sK6(sK2)) | spl8_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f291])).
% 0.21/0.55  fof(f302,plain,(
% 0.21/0.55    ~spl8_5 | ~spl8_6 | spl8_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f299,f287,f283,f279])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    spl8_5 <=> v2_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    spl8_6 <=> l1_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.55  fof(f299,plain,(
% 0.21/0.55    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl8_7),
% 0.21/0.55    inference(resolution,[],[f289,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0] : ((v3_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v3_pre_topc(sK6(X0),X0) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_tops_1)).
% 0.21/0.55  fof(f289,plain,(
% 0.21/0.55    ~m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | spl8_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f287])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    spl8_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f297])).
% 0.21/0.55  fof(f297,plain,(
% 0.21/0.55    $false | spl8_6),
% 0.21/0.55    inference(resolution,[],[f285,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    l1_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f15,f32,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.55  fof(f285,plain,(
% 0.21/0.55    ~l1_pre_topc(sK2) | spl8_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f283])).
% 0.21/0.55  fof(f296,plain,(
% 0.21/0.55    spl8_5),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f295])).
% 0.21/0.55  fof(f295,plain,(
% 0.21/0.55    $false | spl8_5),
% 0.21/0.55    inference(resolution,[],[f281,f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    v2_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    ~v2_pre_topc(sK2) | spl8_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f279])).
% 0.21/0.55  fof(f294,plain,(
% 0.21/0.55    ~spl8_5 | ~spl8_6 | ~spl8_7 | ~spl8_8 | spl8_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f276,f98,f291,f287,f283,f279])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    spl8_2 <=> sP0(k1_xboole_0,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.55  fof(f276,plain,(
% 0.21/0.55    k1_xboole_0 != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,sK6(sK2)) | ~m1_subset_1(sK6(sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl8_2),
% 0.21/0.55    inference(resolution,[],[f275,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X0] : (v3_pre_topc(sK6(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f41])).
% 0.21/0.55  fof(f275,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_pre_topc(X0,sK2) | k1_xboole_0 != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl8_2),
% 0.21/0.55    inference(forward_demodulation,[],[f274,f107])).
% 0.21/0.55  fof(f107,plain,(
% 0.21/0.55    k1_xboole_0 = sK4(k1_xboole_0,sK2) | spl8_2),
% 0.21/0.55    inference(resolution,[],[f103,f64])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    r1_tarski(sK4(k1_xboole_0,sK2),k1_xboole_0) | spl8_2),
% 0.21/0.55    inference(resolution,[],[f100,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP0(X0,X1) | r1_tarski(sK4(X0,X1),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f36,f38,f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) => (k9_subset_1(u1_struct_0(X1),X0,sK5(X0,X1,X4)) = X4 & v3_pre_topc(sK5(X0,X1,X4),X1) & m1_subset_1(sK5(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X1),X0,X3) != X2 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X1),X0,X5) = X4 & v3_pre_topc(X5,X1) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ~sP0(k1_xboole_0,sK2) | spl8_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f98])).
% 0.21/0.55  fof(f274,plain,(
% 0.21/0.55    ( ! [X0] : (sK4(k1_xboole_0,sK2) != k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) | ~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | spl8_2),
% 0.21/0.55    inference(resolution,[],[f62,f100])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (sP0(X0,X1) | k9_subset_1(u1_struct_0(X1),X0,X3) != sK4(X0,X1) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl8_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f163])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    $false | spl8_3),
% 0.21/0.55    inference(resolution,[],[f157,f53])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl8_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f155])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl8_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    $false | spl8_1),
% 0.21/0.55    inference(resolution,[],[f96,f53])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) | spl8_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl8_1 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ~spl8_1 | ~spl8_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f92,f98,f94])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ~sP0(k1_xboole_0,sK2) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    inference(resolution,[],[f90,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ~v2_tex_2(k1_xboole_0,sK2)),
% 0.21/0.55    inference(backward_demodulation,[],[f52,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    k1_xboole_0 = sK3),
% 0.21/0.55    inference(resolution,[],[f54,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    v1_xboole_0(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ~v2_tex_2(sK3,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X0] : (v2_tex_2(X0,sK2) | ~sP0(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.55    inference(resolution,[],[f88,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | ~sP0(X1,X0) | v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X1] : (((v2_tex_2(X1,X0) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_tex_2(X1,X0))) | ~sP1(X0,X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : ((v2_tex_2(X1,X0) <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X0] : (sP1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.55    inference(resolution,[],[f63,f49])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (sP1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(definition_folding,[],[f18,f29,f28])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (32399)------------------------------
% 0.21/0.55  % (32399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32399)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (32399)Memory used [KB]: 6524
% 0.21/0.55  % (32399)Time elapsed: 0.147 s
% 0.21/0.55  % (32399)------------------------------
% 0.21/0.55  % (32399)------------------------------
% 0.21/0.55  % (32409)Refutation not found, incomplete strategy% (32409)------------------------------
% 0.21/0.55  % (32409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32409)Memory used [KB]: 10746
% 0.21/0.55  % (32409)Time elapsed: 0.145 s
% 0.21/0.55  % (32409)------------------------------
% 0.21/0.55  % (32409)------------------------------
% 0.21/0.55  % (32404)Refutation not found, incomplete strategy% (32404)------------------------------
% 0.21/0.55  % (32404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (32404)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (32404)Memory used [KB]: 10746
% 0.21/0.55  % (32404)Time elapsed: 0.147 s
% 0.21/0.55  % (32404)------------------------------
% 0.21/0.55  % (32404)------------------------------
% 0.21/0.56  % (32401)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (32413)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (32395)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (32416)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (32405)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (32407)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (32411)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (32414)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (32415)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (32397)Refutation not found, incomplete strategy% (32397)------------------------------
% 0.21/0.57  % (32397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32397)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32397)Memory used [KB]: 10746
% 0.21/0.57  % (32397)Time elapsed: 0.139 s
% 0.21/0.57  % (32397)------------------------------
% 0.21/0.57  % (32397)------------------------------
% 0.21/0.57  % (32392)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (32400)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.63/0.57  % (32386)Success in time 0.21 s
%------------------------------------------------------------------------------
