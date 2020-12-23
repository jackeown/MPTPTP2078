%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 170 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  329 ( 588 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f78,f83,f88,f101,f109,f114,f162,f173,f207,f300,f382])).

fof(f382,plain,
    ( spl7_15
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl7_15
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f379,f195])).

fof(f195,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0,sK3)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_15
  <=> sP0(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f379,plain,
    ( sP0(k1_xboole_0,k1_xboole_0,sK3)
    | ~ spl7_18 ),
    inference(superposition,[],[f365,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f365,plain,
    ( ! [X0] : sP0(k3_xboole_0(X0,k1_xboole_0),X0,sK3)
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f356,f263])).

fof(f263,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f356,plain,
    ( ! [X0] : sP0(k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0),X0,sK3)
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f299,f45,f63])).

fof(f63,plain,(
    ! [X2,X3,X1] :
      ( sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2)
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X2),X1,X3) != X0
      | ~ v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0
          & v3_pre_topc(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0
        & v3_pre_topc(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X2),X1,X3) != X0
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X2),X1,X4) = X0
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f299,plain,
    ( v3_pre_topc(k1_xboole_0,sK3)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl7_18
  <=> v3_pre_topc(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f300,plain,
    ( spl7_18
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f290,f111,f85,f80,f297])).

fof(f80,plain,
    ( spl7_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f85,plain,
    ( spl7_5
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f111,plain,
    ( spl7_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f290,plain,
    ( v3_pre_topc(k1_xboole_0,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f87,f82,f113,f45,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f113,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f82,plain,
    ( l1_pre_topc(sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( v2_pre_topc(sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f207,plain,
    ( ~ spl7_15
    | spl7_12 ),
    inference(avatar_split_clause,[],[f174,f168,f193])).

fof(f168,plain,
    ( spl7_12
  <=> sP1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f174,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0,sK3)
    | spl7_12 ),
    inference(unit_resulting_resolution,[],[f170,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X0)
      | sP1(X0,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,k1_xboole_0,X0)
      | sP1(X0,k1_xboole_0)
      | sP1(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f52,f134])).

fof(f134,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK5(X0,k1_xboole_0)
      | sP1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f51,f58])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK5(X0,X1),X1)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ~ sP0(sK5(X0,X1),X1,X0)
          & r1_tarski(sK5(X0,X1),X1)
          & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP0(sK5(X0,X1),X1,X0)
        & r1_tarski(sK5(X0,X1),X1)
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( sP0(X3,X1,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ~ sP0(X2,X1,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( sP0(X2,X1,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( sP0(X2,X1,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ sP0(sK5(X0,X1),X1,X0)
      | sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,
    ( ~ sP1(sK3,k1_xboole_0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f173,plain,
    ( ~ spl7_12
    | spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f172,f159,f106,f168])).

fof(f106,plain,
    ( spl7_8
  <=> v2_tex_2(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f159,plain,
    ( spl7_11
  <=> sP2(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f172,plain,
    ( ~ sP1(sK3,k1_xboole_0)
    | spl7_8
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f164,f108])).

fof(f108,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f106])).

fof(f164,plain,
    ( ~ sP1(sK3,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK3)
    | ~ spl7_11 ),
    inference(resolution,[],[f161,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | v2_tex_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v2_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v2_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ( ( v2_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v2_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ( v2_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f161,plain,
    ( sP2(k1_xboole_0,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( spl7_11
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f154,f80,f159])).

fof(f154,plain,
    ( sP2(k1_xboole_0,sK3)
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f82,f45,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f15,f24,f23,f22])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f114,plain,
    ( spl7_9
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f104,f98,f75,f111])).

fof(f75,plain,
    ( spl7_3
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f98,plain,
    ( spl7_7
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f104,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f77,f100])).

fof(f100,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f98])).

fof(f77,plain,
    ( v1_xboole_0(sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f109,plain,
    ( ~ spl7_8
    | spl7_1
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f102,f98,f65,f106])).

fof(f65,plain,
    ( spl7_1
  <=> v2_tex_2(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f102,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK3)
    | spl7_1
    | ~ spl7_7 ),
    inference(backward_demodulation,[],[f67,f100])).

fof(f67,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f101,plain,
    ( spl7_7
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f94,f75,f98])).

fof(f94,plain,
    ( k1_xboole_0 = sK4
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f88,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f40,f85])).

fof(f40,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK3)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & v1_xboole_0(X1) )
   => ( ~ v2_tex_2(sK4,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f83,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f42,f75])).

fof(f42,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f44,f65])).

fof(f44,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (849)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (864)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (858)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (848)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (848)Refutation not found, incomplete strategy% (848)------------------------------
% 0.21/0.47  % (848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (848)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (848)Memory used [KB]: 6140
% 0.21/0.47  % (848)Time elapsed: 0.061 s
% 0.21/0.47  % (848)------------------------------
% 0.21/0.47  % (848)------------------------------
% 0.21/0.47  % (849)Refutation not found, incomplete strategy% (849)------------------------------
% 0.21/0.47  % (849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (849)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (849)Memory used [KB]: 10618
% 0.21/0.47  % (849)Time elapsed: 0.062 s
% 0.21/0.47  % (849)------------------------------
% 0.21/0.47  % (849)------------------------------
% 0.21/0.47  % (864)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f384,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f68,f78,f83,f88,f101,f109,f114,f162,f173,f207,f300,f382])).
% 0.21/0.48  fof(f382,plain,(
% 0.21/0.48    spl7_15 | ~spl7_18),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f381])).
% 0.21/0.48  fof(f381,plain,(
% 0.21/0.48    $false | (spl7_15 | ~spl7_18)),
% 0.21/0.48    inference(subsumption_resolution,[],[f379,f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ~sP0(k1_xboole_0,k1_xboole_0,sK3) | spl7_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f193])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    spl7_15 <=> sP0(k1_xboole_0,k1_xboole_0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.48  fof(f379,plain,(
% 0.21/0.48    sP0(k1_xboole_0,k1_xboole_0,sK3) | ~spl7_18),
% 0.21/0.48    inference(superposition,[],[f365,f119])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f60,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.48  fof(f365,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(k3_xboole_0(X0,k1_xboole_0),X0,sK3)) ) | ~spl7_18),
% 0.21/0.48    inference(forward_demodulation,[],[f356,f263])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f45,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ( ! [X0] : (sP0(k9_subset_1(u1_struct_0(sK3),X0,k1_xboole_0),X0,sK3)) ) | ~spl7_18),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f299,f45,f63])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (sP0(k9_subset_1(u1_struct_0(X2),X1,X3),X1,X2) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.48    inference(equality_resolution,[],[f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0 & v3_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f36,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X2),X1,sK6(X0,X1,X2)) = X0 & v3_pre_topc(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X2),X1,X3) != X0 | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X2),X1,X4) = X0 & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.48    inference(rectify,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X2,X1,X0)))),
% 0.21/0.48    inference(nnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    v3_pre_topc(k1_xboole_0,sK3) | ~spl7_18),
% 0.21/0.48    inference(avatar_component_clause,[],[f297])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    spl7_18 <=> v3_pre_topc(k1_xboole_0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    spl7_18 | ~spl7_4 | ~spl7_5 | ~spl7_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f290,f111,f85,f80,f297])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl7_4 <=> l1_pre_topc(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl7_5 <=> v2_pre_topc(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    spl7_9 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.48  fof(f290,plain,(
% 0.21/0.48    v3_pre_topc(k1_xboole_0,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_9)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f87,f82,f113,f45,f59])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl7_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f111])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    l1_pre_topc(sK3) | ~spl7_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v2_pre_topc(sK3) | ~spl7_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f85])).
% 0.21/0.48  fof(f207,plain,(
% 0.21/0.48    ~spl7_15 | spl7_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f174,f168,f193])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    spl7_12 <=> sP1(sK3,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ~sP0(k1_xboole_0,k1_xboole_0,sK3) | spl7_12),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f170,f150])).
% 0.21/0.48  fof(f150,plain,(
% 0.21/0.48    ( ! [X0] : (~sP0(k1_xboole_0,k1_xboole_0,X0) | sP1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f149])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~sP0(k1_xboole_0,k1_xboole_0,X0) | sP1(X0,k1_xboole_0) | sP1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(superposition,[],[f52,f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = sK5(X0,k1_xboole_0) | sP1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f51,f58])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(sK5(X0,X1),X1) | sP1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(sK5(X0,X1),X1,X0) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f32,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~sP0(sK5(X0,X1),X1,X0) & r1_tarski(sK5(X0,X1),X1) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (sP0(X3,X1,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(rectify,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : (~sP0(X2,X1,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP1(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (sP0(X2,X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP0(sK5(X0,X1),X1,X0) | sP1(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ~sP1(sK3,k1_xboole_0) | spl7_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f168])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    ~spl7_12 | spl7_8 | ~spl7_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f172,f159,f106,f168])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    spl7_8 <=> v2_tex_2(k1_xboole_0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    spl7_11 <=> sP2(k1_xboole_0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    ~sP1(sK3,k1_xboole_0) | (spl7_8 | ~spl7_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f164,f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    ~v2_tex_2(k1_xboole_0,sK3) | spl7_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f106])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ~sP1(sK3,k1_xboole_0) | v2_tex_2(k1_xboole_0,sK3) | ~spl7_11),
% 0.21/0.48    inference(resolution,[],[f161,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~sP2(X0,X1) | ~sP1(X1,X0) | v2_tex_2(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1] : (((v2_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v2_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.48    inference(rectify,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X1,X0] : (((v2_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v2_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X1,X0] : ((v2_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    sP2(k1_xboole_0,sK3) | ~spl7_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f159])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    spl7_11 | ~spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f154,f80,f159])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    sP2(k1_xboole_0,sK3) | ~spl7_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f82,f45,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(definition_folding,[],[f15,f24,f23,f22])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl7_9 | ~spl7_3 | ~spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f104,f98,f75,f111])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl7_3 <=> v1_xboole_0(sK4)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    spl7_7 <=> k1_xboole_0 = sK4),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | (~spl7_3 | ~spl7_7)),
% 0.21/0.48    inference(backward_demodulation,[],[f77,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    k1_xboole_0 = sK4 | ~spl7_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f98])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v1_xboole_0(sK4) | ~spl7_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f75])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~spl7_8 | spl7_1 | ~spl7_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f102,f98,f65,f106])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl7_1 <=> v2_tex_2(sK4,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~v2_tex_2(k1_xboole_0,sK3) | (spl7_1 | ~spl7_7)),
% 0.21/0.48    inference(backward_demodulation,[],[f67,f100])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v2_tex_2(sK4,sK3) | spl7_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl7_7 | ~spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f94,f75,f98])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    k1_xboole_0 = sK4 | ~spl7_3),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f77,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl7_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f85])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v2_pre_topc(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f12,f27,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl7_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f80])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    l1_pre_topc(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl7_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f75])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v1_xboole_0(sK4)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~spl7_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f65])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ~v2_tex_2(sK4,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (864)------------------------------
% 0.21/0.48  % (864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (864)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (864)Memory used [KB]: 10874
% 0.21/0.48  % (864)Time elapsed: 0.073 s
% 0.21/0.48  % (864)------------------------------
% 0.21/0.48  % (864)------------------------------
% 0.21/0.48  % (847)Success in time 0.127 s
%------------------------------------------------------------------------------
