%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 158 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  263 ( 460 expanded)
%              Number of equality atoms :   23 (  36 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f76,f81,f91,f98,f106,f111,f180,f203,f322,f334,f387,f417,f786])).

fof(f786,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_12
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f785,f414,f200,f68,f103])).

fof(f103,plain,
    ( spl8_7
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f68,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f200,plain,
    ( spl8_12
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f414,plain,
    ( spl8_25
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f785,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl8_12
    | ~ spl8_25 ),
    inference(trivial_inequality_removal,[],[f784])).

fof(f784,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl8_12
    | ~ spl8_25 ),
    inference(forward_demodulation,[],[f783,f416])).

fof(f416,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f414])).

fof(f783,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f446,f202])).

fof(f202,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f200])).

fof(f446,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | k1_xboole_0 != sK2(X1,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f441,f128])).

fof(f128,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X1) = X1 ),
    inference(global_subsumption,[],[f115,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ sP6(X0) ) ),
    inference(general_splitting,[],[f58,f63_D])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP6(X0) ) ),
    inference(cnf_transformation,[],[f63_D])).

fof(f63_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP6(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f115,plain,(
    ! [X0] : sP6(X0) ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f441,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | ~ v3_pre_topc(k1_xboole_0,X1)
      | sK2(X1,k1_xboole_0) != k9_subset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f228,f40])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f42,f40])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(f417,plain,
    ( spl8_25
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f407,f327,f414])).

fof(f327,plain,
    ( spl8_15
  <=> v1_xboole_0(sK2(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f407,plain,
    ( k1_xboole_0 = sK2(sK0,k1_xboole_0)
    | ~ spl8_15 ),
    inference(resolution,[],[f329,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f329,plain,
    ( v1_xboole_0(sK2(sK0,k1_xboole_0))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f327])).

fof(f387,plain,
    ( ~ spl8_8
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f385,f331,f108])).

fof(f108,plain,
    ( spl8_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f331,plain,
    ( spl8_16
  <=> r2_hidden(sK4(sK2(sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f385,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_16 ),
    inference(resolution,[],[f333,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f333,plain,
    ( r2_hidden(sK4(sK2(sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f331])).

fof(f334,plain,
    ( spl8_15
    | spl8_16
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f323,f319,f331,f327])).

fof(f319,plain,
    ( spl8_14
  <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f323,plain,
    ( r2_hidden(sK4(sK2(sK0,k1_xboole_0)),k1_xboole_0)
    | v1_xboole_0(sK2(sK0,k1_xboole_0))
    | ~ spl8_14 ),
    inference(resolution,[],[f321,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK4(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f321,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f319])).

fof(f322,plain,
    ( spl8_7
    | spl8_14
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f317,f68,f319,f103])).

fof(f317,plain,
    ( r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK0)
    | ~ spl8_1 ),
    inference(resolution,[],[f189,f70])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f189,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f203,plain,
    ( ~ spl8_2
    | spl8_12
    | ~ spl8_1
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f198,f178,f68,f200,f73])).

fof(f73,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f178,plain,
    ( spl8_11
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v3_pre_topc(k1_xboole_0,X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f198,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl8_1
    | ~ spl8_11 ),
    inference(resolution,[],[f179,f70])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | v3_pre_topc(k1_xboole_0,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f180,plain,
    ( ~ spl8_8
    | spl8_11 ),
    inference(avatar_split_clause,[],[f173,f178,f108])).

fof(f173,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v3_pre_topc(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f49,f40])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).

fof(f111,plain,
    ( spl8_8
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f101,f95,f88,f108])).

fof(f88,plain,
    ( spl8_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f95,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f101,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f90,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f90,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f106,plain,
    ( ~ spl8_7
    | spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f100,f95,f78,f103])).

fof(f78,plain,
    ( spl8_3
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f100,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | spl8_3
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f80,f97])).

fof(f80,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f98,plain,
    ( spl8_6
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f93,f88,f95])).

fof(f93,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_5 ),
    inference(resolution,[],[f48,f90])).

fof(f91,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f34,f88])).

fof(f34,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f81,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f36,f78])).

fof(f36,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f76,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f37,f73])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f38,f68])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (8592)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (8585)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.51  % (8575)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (8573)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (8590)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (8581)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (8585)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f787,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f71,f76,f81,f91,f98,f106,f111,f180,f203,f322,f334,f387,f417,f786])).
% 0.22/0.55  fof(f786,plain,(
% 0.22/0.55    spl8_7 | ~spl8_1 | ~spl8_12 | ~spl8_25),
% 0.22/0.55    inference(avatar_split_clause,[],[f785,f414,f200,f68,f103])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    spl8_7 <=> v2_tex_2(k1_xboole_0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl8_1 <=> l1_pre_topc(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    spl8_12 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.22/0.55  fof(f414,plain,(
% 0.22/0.55    spl8_25 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.22/0.55  fof(f785,plain,(
% 0.22/0.55    ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl8_12 | ~spl8_25)),
% 0.22/0.55    inference(trivial_inequality_removal,[],[f784])).
% 0.22/0.55  fof(f784,plain,(
% 0.22/0.55    k1_xboole_0 != k1_xboole_0 | ~l1_pre_topc(sK0) | v2_tex_2(k1_xboole_0,sK0) | (~spl8_12 | ~spl8_25)),
% 0.22/0.55    inference(forward_demodulation,[],[f783,f416])).
% 0.22/0.55  fof(f416,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl8_25),
% 0.22/0.55    inference(avatar_component_clause,[],[f414])).
% 0.22/0.55  fof(f783,plain,(
% 0.22/0.55    ~l1_pre_topc(sK0) | k1_xboole_0 != sK2(sK0,k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~spl8_12),
% 0.22/0.55    inference(resolution,[],[f446,f202])).
% 0.22/0.55  fof(f202,plain,(
% 0.22/0.55    v3_pre_topc(k1_xboole_0,sK0) | ~spl8_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f200])).
% 0.22/0.55  fof(f446,plain,(
% 0.22/0.55    ( ! [X1] : (~v3_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | k1_xboole_0 != sK2(X1,k1_xboole_0) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f441,f128])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1) )),
% 0.22/0.55    inference(global_subsumption,[],[f115,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~sP6(X0)) )),
% 0.22/0.55    inference(general_splitting,[],[f58,f63_D])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP6(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f63_D])).
% 0.22/0.55  fof(f63_D,plain,(
% 0.22/0.55    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP6(X0)) )),
% 0.22/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 0.22/0.55  fof(f115,plain,(
% 0.22/0.55    ( ! [X0] : (sP6(X0)) )),
% 0.22/0.55    inference(resolution,[],[f63,f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.55  fof(f441,plain,(
% 0.22/0.55    ( ! [X1] : (~l1_pre_topc(X1) | ~v3_pre_topc(k1_xboole_0,X1) | sK2(X1,k1_xboole_0) != k9_subset_1(u1_struct_0(X1),k1_xboole_0,k1_xboole_0) | v2_tex_2(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(resolution,[],[f228,f40])).
% 0.22/0.55  fof(f228,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | sK2(X0,k1_xboole_0) != k9_subset_1(u1_struct_0(X0),k1_xboole_0,X1) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f42,f40])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).
% 0.22/0.55  fof(f417,plain,(
% 0.22/0.55    spl8_25 | ~spl8_15),
% 0.22/0.55    inference(avatar_split_clause,[],[f407,f327,f414])).
% 0.22/0.55  fof(f327,plain,(
% 0.22/0.55    spl8_15 <=> v1_xboole_0(sK2(sK0,k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.55  fof(f407,plain,(
% 0.22/0.55    k1_xboole_0 = sK2(sK0,k1_xboole_0) | ~spl8_15),
% 0.22/0.55    inference(resolution,[],[f329,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.55  fof(f329,plain,(
% 0.22/0.55    v1_xboole_0(sK2(sK0,k1_xboole_0)) | ~spl8_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f327])).
% 0.22/0.55  fof(f387,plain,(
% 0.22/0.55    ~spl8_8 | ~spl8_16),
% 0.22/0.55    inference(avatar_split_clause,[],[f385,f331,f108])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    spl8_8 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.55  fof(f331,plain,(
% 0.22/0.55    spl8_16 <=> r2_hidden(sK4(sK2(sK0,k1_xboole_0)),k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.55  fof(f385,plain,(
% 0.22/0.55    ~v1_xboole_0(k1_xboole_0) | ~spl8_16),
% 0.22/0.55    inference(resolution,[],[f333,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.55  fof(f333,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2(sK0,k1_xboole_0)),k1_xboole_0) | ~spl8_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f331])).
% 0.22/0.55  fof(f334,plain,(
% 0.22/0.55    spl8_15 | spl8_16 | ~spl8_14),
% 0.22/0.55    inference(avatar_split_clause,[],[f323,f319,f331,f327])).
% 0.22/0.55  fof(f319,plain,(
% 0.22/0.55    spl8_14 <=> r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.22/0.55  fof(f323,plain,(
% 0.22/0.55    r2_hidden(sK4(sK2(sK0,k1_xboole_0)),k1_xboole_0) | v1_xboole_0(sK2(sK0,k1_xboole_0)) | ~spl8_14),
% 0.22/0.55    inference(resolution,[],[f321,f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK4(X0),X1) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(resolution,[],[f53,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f1])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f321,plain,(
% 0.22/0.55    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | ~spl8_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f319])).
% 0.22/0.55  fof(f322,plain,(
% 0.22/0.55    spl8_7 | spl8_14 | ~spl8_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f317,f68,f319,f103])).
% 0.22/0.55  fof(f317,plain,(
% 0.22/0.55    r1_tarski(sK2(sK0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,sK0) | ~spl8_1),
% 0.22/0.55    inference(resolution,[],[f189,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    l1_pre_topc(sK0) | ~spl8_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | r1_tarski(sK2(X0,k1_xboole_0),k1_xboole_0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f47,f40])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(sK2(X0,X1),X1) | v2_tex_2(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f203,plain,(
% 0.22/0.55    ~spl8_2 | spl8_12 | ~spl8_1 | ~spl8_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f198,f178,f68,f200,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    spl8_2 <=> v2_pre_topc(sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    spl8_11 <=> ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    v3_pre_topc(k1_xboole_0,sK0) | ~v2_pre_topc(sK0) | (~spl8_1 | ~spl8_11)),
% 0.22/0.55    inference(resolution,[],[f179,f70])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | v3_pre_topc(k1_xboole_0,X0) | ~v2_pre_topc(X0)) ) | ~spl8_11),
% 0.22/0.55    inference(avatar_component_clause,[],[f178])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    ~spl8_8 | spl8_11),
% 0.22/0.55    inference(avatar_split_clause,[],[f173,f178,f108])).
% 0.22/0.55  fof(f173,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v3_pre_topc(k1_xboole_0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f49,f40])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_xboole_0(X1) | v3_pre_topc(X1,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,axiom,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tops_1)).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    spl8_8 | ~spl8_5 | ~spl8_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f101,f95,f88,f108])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    spl8_5 <=> v1_xboole_0(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl8_6 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    v1_xboole_0(k1_xboole_0) | (~spl8_5 | ~spl8_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f90,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl8_6),
% 0.22/0.55    inference(avatar_component_clause,[],[f95])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    v1_xboole_0(sK1) | ~spl8_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f88])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    ~spl8_7 | spl8_3 | ~spl8_6),
% 0.22/0.55    inference(avatar_split_clause,[],[f100,f95,f78,f103])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    spl8_3 <=> v2_tex_2(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.55  fof(f100,plain,(
% 0.22/0.55    ~v2_tex_2(k1_xboole_0,sK0) | (spl8_3 | ~spl8_6)),
% 0.22/0.55    inference(backward_demodulation,[],[f80,f97])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ~v2_tex_2(sK1,sK0) | spl8_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f78])).
% 0.22/0.55  fof(f98,plain,(
% 0.22/0.55    spl8_6 | ~spl8_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f93,f88,f95])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl8_5),
% 0.22/0.55    inference(resolution,[],[f48,f90])).
% 0.22/0.55  fof(f91,plain,(
% 0.22/0.55    spl8_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f34,f88])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    v1_xboole_0(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.55    inference(flattening,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ~spl8_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f36,f78])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ~v2_tex_2(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    spl8_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f37,f73])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    v2_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    spl8_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f38,f68])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    l1_pre_topc(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (8585)------------------------------
% 0.22/0.55  % (8585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8585)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (8585)Memory used [KB]: 11385
% 0.22/0.55  % (8585)Time elapsed: 0.089 s
% 0.22/0.55  % (8585)------------------------------
% 0.22/0.55  % (8585)------------------------------
% 0.22/0.56  % (8565)Success in time 0.194 s
%------------------------------------------------------------------------------
