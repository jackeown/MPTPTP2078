%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:09 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 312 expanded)
%              Number of leaves         :   39 ( 137 expanded)
%              Depth                    :    7
%              Number of atoms          :  548 (1064 expanded)
%              Number of equality atoms :    5 (  11 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f104,f109,f139,f144,f152,f158,f171,f183,f188,f201,f219,f226,f236,f258,f264,f267,f275,f282,f292,f297,f301,f315,f318])).

fof(f318,plain,
    ( ~ spl6_27
    | ~ spl6_33
    | spl6_34 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl6_27
    | ~ spl6_33
    | spl6_34 ),
    inference(unit_resulting_resolution,[],[f296,f235,f314,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f314,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl6_34
  <=> r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f235,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl6_27
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f296,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl6_33
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f315,plain,
    ( ~ spl6_34
    | spl6_22 ),
    inference(avatar_split_clause,[],[f307,f198,f312])).

fof(f198,plain,
    ( spl6_22
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f307,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0))
    | spl6_22 ),
    inference(resolution,[],[f200,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f200,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f198])).

fof(f301,plain,
    ( spl6_21
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl6_21
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f263,f196,f75])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k2_tarski(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f48])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f196,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | spl6_21 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_21
  <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f263,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl6_32
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f297,plain,
    ( spl6_33
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f289,f212,f294])).

fof(f212,plain,
    ( spl6_25
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f289,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl6_25 ),
    inference(resolution,[],[f213,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f213,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f212])).

fof(f292,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25
    | spl6_26 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_25
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f81,f91,f86,f218,f96,f170,f213,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f170,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl6_16
  <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f96,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f218,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl6_26
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f86,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f91,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f282,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | spl6_25 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_19
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f81,f91,f86,f187,f96,f214,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f214,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f212])).

fof(f187,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl6_19
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f275,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_23
    | spl6_24 ),
    inference(avatar_contradiction_clause,[],[f271])).

fof(f271,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_23
    | spl6_24 ),
    inference(unit_resulting_resolution,[],[f81,f91,f86,f210,f96,f205,f157,f42])).

fof(f157,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl6_14
  <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl6_23
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f210,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | spl6_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl6_24
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f267,plain,
    ( ~ spl6_11
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl6_11
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f138,f263,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f138,plain,
    ( v1_xboole_0(sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_11
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f264,plain,
    ( ~ spl6_4
    | spl6_32
    | ~ spl6_18
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f259,f256,f180,f261,f94])).

fof(f180,plain,
    ( spl6_18
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f256,plain,
    ( spl6_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK3)
        | ~ m1_connsp_2(sK3,sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f259,plain,
    ( r2_hidden(sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_18
    | ~ spl6_31 ),
    inference(resolution,[],[f257,f182])).

fof(f182,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl6_31
    | spl6_1
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f227,f204,f84,f89,f79,f256])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,sK3) )
    | ~ spl6_23 ),
    inference(resolution,[],[f205,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f236,plain,
    ( spl6_27
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f229,f204,f233])).

fof(f229,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl6_23 ),
    inference(resolution,[],[f205,f56])).

fof(f226,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | spl6_23 ),
    inference(unit_resulting_resolution,[],[f81,f91,f86,f182,f96,f206,f54])).

fof(f206,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f219,plain,
    ( ~ spl6_2
    | ~ spl6_23
    | ~ spl6_24
    | ~ spl6_25
    | ~ spl6_26
    | ~ spl6_3
    | spl6_20 ),
    inference(avatar_split_clause,[],[f202,f190,f89,f216,f212,f208,f204,f84])).

fof(f190,plain,
    ( spl6_20
  <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f202,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | spl6_20 ),
    inference(resolution,[],[f192,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f192,plain,
    ( ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | spl6_20 ),
    inference(avatar_component_clause,[],[f190])).

fof(f201,plain,
    ( spl6_1
    | ~ spl6_20
    | ~ spl6_21
    | ~ spl6_22
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | spl6_13 ),
    inference(avatar_split_clause,[],[f153,f149,f84,f89,f94,f198,f194,f190,f79])).

fof(f149,plain,
    ( spl6_13
  <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f153,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)
    | v2_struct_0(sK0)
    | spl6_13 ),
    inference(resolution,[],[f151,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f151,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f188,plain,
    ( spl6_19
    | spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f122,f106,f84,f89,f94,f79,f185])).

fof(f106,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f122,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f108,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f108,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f183,plain,
    ( spl6_18
    | spl6_1
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f119,f101,f84,f89,f94,f79,f180])).

fof(f101,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f119,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_5 ),
    inference(resolution,[],[f103,f44])).

fof(f103,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f171,plain,
    ( spl6_10
    | spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f124,f106,f168,f132])).

fof(f132,plain,
    ( spl6_10
  <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f124,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_6 ),
    inference(resolution,[],[f108,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f158,plain,
    ( spl6_10
    | spl6_14
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f121,f101,f155,f132])).

fof(f121,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_5 ),
    inference(resolution,[],[f103,f52])).

fof(f152,plain,
    ( ~ spl6_13
    | spl6_12 ),
    inference(avatar_split_clause,[],[f145,f141,f149])).

fof(f141,plain,
    ( spl6_12
  <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f145,plain,
    ( ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_12 ),
    inference(resolution,[],[f143,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f143,plain,
    ( ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl6_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f144,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f66,f141])).

fof(f66,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f35,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f139,plain,
    ( ~ spl6_10
    | spl6_11
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f120,f101,f136,f132])).

fof(f120,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl6_5 ),
    inference(resolution,[],[f103,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f36,f106])).

fof(f36,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f34,f101])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f92,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f87,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f39,f84])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f38,f79])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:49:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (12183)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (12201)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (12182)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (12181)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.52  % (12177)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (12193)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.52  % (12196)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.52  % (12184)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.23/0.53  % (12204)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.53  % (12197)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.53  % (12179)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.53  % (12188)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.53  % (12185)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.23/0.53  % (12178)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (12185)Refutation not found, incomplete strategy% (12185)------------------------------
% 1.23/0.53  % (12185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (12185)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (12185)Memory used [KB]: 10618
% 1.23/0.53  % (12185)Time elapsed: 0.132 s
% 1.23/0.53  % (12185)------------------------------
% 1.23/0.53  % (12185)------------------------------
% 1.23/0.53  % (12176)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.53  % (12191)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.23/0.53  % (12190)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.23/0.53  % (12175)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.53  % (12199)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.53  % (12197)Refutation found. Thanks to Tanya!
% 1.39/0.53  % SZS status Theorem for theBenchmark
% 1.39/0.53  % SZS output start Proof for theBenchmark
% 1.39/0.53  fof(f319,plain,(
% 1.39/0.53    $false),
% 1.39/0.53    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f104,f109,f139,f144,f152,f158,f171,f183,f188,f201,f219,f226,f236,f258,f264,f267,f275,f282,f292,f297,f301,f315,f318])).
% 1.39/0.53  fof(f318,plain,(
% 1.39/0.53    ~spl6_27 | ~spl6_33 | spl6_34),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f316])).
% 1.39/0.53  fof(f316,plain,(
% 1.39/0.53    $false | (~spl6_27 | ~spl6_33 | spl6_34)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f296,f235,f314,f68])).
% 1.39/0.53  fof(f68,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(definition_unfolding,[],[f58,f48])).
% 1.39/0.53  fof(f48,plain,(
% 1.39/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.39/0.53    inference(cnf_transformation,[],[f4])).
% 1.39/0.53  fof(f4,axiom,(
% 1.39/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.39/0.53  fof(f58,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f31])).
% 1.39/0.53  fof(f31,plain,(
% 1.39/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.39/0.53    inference(flattening,[],[f30])).
% 1.39/0.53  fof(f30,plain,(
% 1.39/0.53    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.39/0.53    inference(ennf_transformation,[],[f3])).
% 1.39/0.53  fof(f3,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.39/0.53  fof(f314,plain,(
% 1.39/0.53    ~r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) | spl6_34),
% 1.39/0.53    inference(avatar_component_clause,[],[f312])).
% 1.39/0.53  fof(f312,plain,(
% 1.39/0.53    spl6_34 <=> r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 1.39/0.53  fof(f235,plain,(
% 1.39/0.53    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_27),
% 1.39/0.53    inference(avatar_component_clause,[],[f233])).
% 1.39/0.53  fof(f233,plain,(
% 1.39/0.53    spl6_27 <=> r1_tarski(sK3,u1_struct_0(sK0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.39/0.53  fof(f296,plain,(
% 1.39/0.53    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl6_33),
% 1.39/0.53    inference(avatar_component_clause,[],[f294])).
% 1.39/0.53  fof(f294,plain,(
% 1.39/0.53    spl6_33 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 1.39/0.53  fof(f315,plain,(
% 1.39/0.53    ~spl6_34 | spl6_22),
% 1.39/0.53    inference(avatar_split_clause,[],[f307,f198,f312])).
% 1.39/0.53  fof(f198,plain,(
% 1.39/0.53    spl6_22 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.39/0.53  fof(f307,plain,(
% 1.39/0.53    ~r1_tarski(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) | spl6_22),
% 1.39/0.53    inference(resolution,[],[f200,f55])).
% 1.39/0.53  fof(f55,plain,(
% 1.39/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f7])).
% 1.39/0.53  fof(f7,axiom,(
% 1.39/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.53  fof(f200,plain,(
% 1.39/0.53    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_22),
% 1.39/0.53    inference(avatar_component_clause,[],[f198])).
% 1.39/0.53  fof(f301,plain,(
% 1.39/0.53    spl6_21 | ~spl6_32),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f298])).
% 1.39/0.53  fof(f298,plain,(
% 1.39/0.53    $false | (spl6_21 | ~spl6_32)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f263,f196,f75])).
% 1.39/0.53  fof(f75,plain,(
% 1.39/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k2_tarski(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.39/0.53    inference(equality_resolution,[],[f69])).
% 1.39/0.53  fof(f69,plain,(
% 1.39/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 1.39/0.53    inference(definition_unfolding,[],[f65,f48])).
% 1.39/0.53  fof(f65,plain,(
% 1.39/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.39/0.53    inference(cnf_transformation,[],[f2])).
% 1.39/0.53  fof(f2,axiom,(
% 1.39/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.39/0.53  fof(f196,plain,(
% 1.39/0.53    ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | spl6_21),
% 1.39/0.53    inference(avatar_component_clause,[],[f194])).
% 1.39/0.53  fof(f194,plain,(
% 1.39/0.53    spl6_21 <=> r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.39/0.53  fof(f263,plain,(
% 1.39/0.53    r2_hidden(sK1,sK3) | ~spl6_32),
% 1.39/0.53    inference(avatar_component_clause,[],[f261])).
% 1.39/0.53  fof(f261,plain,(
% 1.39/0.53    spl6_32 <=> r2_hidden(sK1,sK3)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.39/0.53  fof(f297,plain,(
% 1.39/0.53    spl6_33 | ~spl6_25),
% 1.39/0.53    inference(avatar_split_clause,[],[f289,f212,f294])).
% 1.39/0.53  fof(f212,plain,(
% 1.39/0.53    spl6_25 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.39/0.53  fof(f289,plain,(
% 1.39/0.53    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl6_25),
% 1.39/0.53    inference(resolution,[],[f213,f56])).
% 1.39/0.53  fof(f56,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f7])).
% 1.39/0.53  fof(f213,plain,(
% 1.39/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_25),
% 1.39/0.53    inference(avatar_component_clause,[],[f212])).
% 1.39/0.53  fof(f292,plain,(
% 1.39/0.53    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25 | spl6_26),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f286])).
% 1.39/0.53  fof(f286,plain,(
% 1.39/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_16 | ~spl6_25 | spl6_26)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f81,f91,f86,f218,f96,f170,f213,f42])).
% 1.39/0.53  fof(f42,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f19])).
% 1.39/0.53  fof(f19,plain,(
% 1.39/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.53    inference(flattening,[],[f18])).
% 1.39/0.53  fof(f18,plain,(
% 1.39/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f12])).
% 1.39/0.53  fof(f12,axiom,(
% 1.39/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.39/0.53  fof(f170,plain,(
% 1.39/0.53    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_16),
% 1.39/0.53    inference(avatar_component_clause,[],[f168])).
% 1.39/0.53  fof(f168,plain,(
% 1.39/0.53    spl6_16 <=> r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.39/0.53  fof(f96,plain,(
% 1.39/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_4),
% 1.39/0.53    inference(avatar_component_clause,[],[f94])).
% 1.39/0.53  fof(f94,plain,(
% 1.39/0.53    spl6_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.39/0.53  fof(f218,plain,(
% 1.39/0.53    ~v3_pre_topc(sK2,sK0) | spl6_26),
% 1.39/0.53    inference(avatar_component_clause,[],[f216])).
% 1.39/0.53  fof(f216,plain,(
% 1.39/0.53    spl6_26 <=> v3_pre_topc(sK2,sK0)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.39/0.53  fof(f86,plain,(
% 1.39/0.53    v2_pre_topc(sK0) | ~spl6_2),
% 1.39/0.53    inference(avatar_component_clause,[],[f84])).
% 1.39/0.53  fof(f84,plain,(
% 1.39/0.53    spl6_2 <=> v2_pre_topc(sK0)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.39/0.53  fof(f91,plain,(
% 1.39/0.53    l1_pre_topc(sK0) | ~spl6_3),
% 1.39/0.53    inference(avatar_component_clause,[],[f89])).
% 1.39/0.53  fof(f89,plain,(
% 1.39/0.53    spl6_3 <=> l1_pre_topc(sK0)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.39/0.53  fof(f81,plain,(
% 1.39/0.53    ~v2_struct_0(sK0) | spl6_1),
% 1.39/0.53    inference(avatar_component_clause,[],[f79])).
% 1.39/0.53  fof(f79,plain,(
% 1.39/0.53    spl6_1 <=> v2_struct_0(sK0)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.39/0.53  fof(f282,plain,(
% 1.39/0.53    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | spl6_25),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f276])).
% 1.39/0.53  fof(f276,plain,(
% 1.39/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_19 | spl6_25)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f81,f91,f86,f187,f96,f214,f54])).
% 1.39/0.53  fof(f54,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f27])).
% 1.39/0.53  fof(f27,plain,(
% 1.39/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.53    inference(flattening,[],[f26])).
% 1.39/0.53  fof(f26,plain,(
% 1.39/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f10])).
% 1.39/0.53  fof(f10,axiom,(
% 1.39/0.53    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.39/0.53  fof(f214,plain,(
% 1.39/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_25),
% 1.39/0.53    inference(avatar_component_clause,[],[f212])).
% 1.39/0.53  fof(f187,plain,(
% 1.39/0.53    m1_connsp_2(sK2,sK0,sK1) | ~spl6_19),
% 1.39/0.53    inference(avatar_component_clause,[],[f185])).
% 1.39/0.53  fof(f185,plain,(
% 1.39/0.53    spl6_19 <=> m1_connsp_2(sK2,sK0,sK1)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.39/0.53  fof(f275,plain,(
% 1.39/0.53    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_14 | ~spl6_23 | spl6_24),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f271])).
% 1.39/0.53  fof(f271,plain,(
% 1.39/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_14 | ~spl6_23 | spl6_24)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f81,f91,f86,f210,f96,f205,f157,f42])).
% 1.39/0.53  fof(f157,plain,(
% 1.39/0.53    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_14),
% 1.39/0.53    inference(avatar_component_clause,[],[f155])).
% 1.39/0.53  fof(f155,plain,(
% 1.39/0.53    spl6_14 <=> r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.39/0.53  fof(f205,plain,(
% 1.39/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_23),
% 1.39/0.53    inference(avatar_component_clause,[],[f204])).
% 1.39/0.53  fof(f204,plain,(
% 1.39/0.53    spl6_23 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.39/0.53  fof(f210,plain,(
% 1.39/0.53    ~v3_pre_topc(sK3,sK0) | spl6_24),
% 1.39/0.53    inference(avatar_component_clause,[],[f208])).
% 1.39/0.53  fof(f208,plain,(
% 1.39/0.53    spl6_24 <=> v3_pre_topc(sK3,sK0)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.39/0.53  fof(f267,plain,(
% 1.39/0.53    ~spl6_11 | ~spl6_32),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f265])).
% 1.39/0.53  fof(f265,plain,(
% 1.39/0.53    $false | (~spl6_11 | ~spl6_32)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f138,f263,f47])).
% 1.39/0.53  fof(f47,plain,(
% 1.39/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f1])).
% 1.39/0.53  fof(f1,axiom,(
% 1.39/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.39/0.53  fof(f138,plain,(
% 1.39/0.53    v1_xboole_0(sK3) | ~spl6_11),
% 1.39/0.53    inference(avatar_component_clause,[],[f136])).
% 1.39/0.53  fof(f136,plain,(
% 1.39/0.53    spl6_11 <=> v1_xboole_0(sK3)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.39/0.53  fof(f264,plain,(
% 1.39/0.53    ~spl6_4 | spl6_32 | ~spl6_18 | ~spl6_31),
% 1.39/0.53    inference(avatar_split_clause,[],[f259,f256,f180,f261,f94])).
% 1.39/0.53  fof(f180,plain,(
% 1.39/0.53    spl6_18 <=> m1_connsp_2(sK3,sK0,sK1)),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.39/0.53  fof(f256,plain,(
% 1.39/0.53    spl6_31 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK3) | ~m1_connsp_2(sK3,sK0,X0))),
% 1.39/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.39/0.53  fof(f259,plain,(
% 1.39/0.53    r2_hidden(sK1,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_18 | ~spl6_31)),
% 1.39/0.53    inference(resolution,[],[f257,f182])).
% 1.39/0.53  fof(f182,plain,(
% 1.39/0.53    m1_connsp_2(sK3,sK0,sK1) | ~spl6_18),
% 1.39/0.53    inference(avatar_component_clause,[],[f180])).
% 1.39/0.53  fof(f257,plain,(
% 1.39/0.53    ( ! [X0] : (~m1_connsp_2(sK3,sK0,X0) | r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_31),
% 1.39/0.53    inference(avatar_component_clause,[],[f256])).
% 1.39/0.53  fof(f258,plain,(
% 1.39/0.53    spl6_31 | spl6_1 | ~spl6_3 | ~spl6_2 | ~spl6_23),
% 1.39/0.53    inference(avatar_split_clause,[],[f227,f204,f84,f89,f79,f256])).
% 1.39/0.53  fof(f227,plain,(
% 1.39/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_connsp_2(sK3,sK0,X0) | r2_hidden(X0,sK3)) ) | ~spl6_23),
% 1.39/0.53    inference(resolution,[],[f205,f45])).
% 1.39/0.53  fof(f45,plain,(
% 1.39/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 1.39/0.53    inference(cnf_transformation,[],[f23])).
% 1.39/0.53  fof(f23,plain,(
% 1.39/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.53    inference(flattening,[],[f22])).
% 1.39/0.53  fof(f22,plain,(
% 1.39/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.53    inference(ennf_transformation,[],[f11])).
% 1.39/0.53  fof(f11,axiom,(
% 1.39/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 1.39/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).
% 1.39/0.53  fof(f236,plain,(
% 1.39/0.53    spl6_27 | ~spl6_23),
% 1.39/0.53    inference(avatar_split_clause,[],[f229,f204,f233])).
% 1.39/0.53  fof(f229,plain,(
% 1.39/0.53    r1_tarski(sK3,u1_struct_0(sK0)) | ~spl6_23),
% 1.39/0.53    inference(resolution,[],[f205,f56])).
% 1.39/0.53  fof(f226,plain,(
% 1.39/0.53    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_18 | spl6_23),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f220])).
% 1.39/0.53  fof(f220,plain,(
% 1.39/0.53    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_18 | spl6_23)),
% 1.39/0.53    inference(unit_resulting_resolution,[],[f81,f91,f86,f182,f96,f206,f54])).
% 1.39/0.53  fof(f206,plain,(
% 1.39/0.53    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl6_23),
% 1.39/0.53    inference(avatar_component_clause,[],[f204])).
% 1.39/0.53  fof(f219,plain,(
% 1.39/0.53    ~spl6_2 | ~spl6_23 | ~spl6_24 | ~spl6_25 | ~spl6_26 | ~spl6_3 | spl6_20),
% 1.39/0.54    inference(avatar_split_clause,[],[f202,f190,f89,f216,f212,f208,f204,f84])).
% 1.39/0.54  fof(f190,plain,(
% 1.39/0.54    spl6_20 <=> v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.39/0.54  fof(f202,plain,(
% 1.39/0.54    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | spl6_20),
% 1.39/0.54    inference(resolution,[],[f192,f67])).
% 1.39/0.54  fof(f67,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 1.39/0.54    inference(definition_unfolding,[],[f57,f48])).
% 1.39/0.54  fof(f57,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k2_xboole_0(X1,X2),X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f29])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.39/0.54    inference(flattening,[],[f28])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f9])).
% 1.39/0.54  fof(f9,axiom,(
% 1.39/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.39/0.54  fof(f192,plain,(
% 1.39/0.54    ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | spl6_20),
% 1.39/0.54    inference(avatar_component_clause,[],[f190])).
% 1.39/0.54  fof(f201,plain,(
% 1.39/0.54    spl6_1 | ~spl6_20 | ~spl6_21 | ~spl6_22 | ~spl6_4 | ~spl6_3 | ~spl6_2 | spl6_13),
% 1.39/0.54    inference(avatar_split_clause,[],[f153,f149,f84,f89,f94,f198,f194,f190,f79])).
% 1.39/0.54  fof(f149,plain,(
% 1.39/0.54    spl6_13 <=> r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.39/0.54  fof(f153,plain,(
% 1.39/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k3_tarski(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) | v2_struct_0(sK0) | spl6_13),
% 1.39/0.54    inference(resolution,[],[f151,f43])).
% 1.39/0.54  fof(f43,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f19])).
% 1.39/0.54  fof(f151,plain,(
% 1.39/0.54    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_13),
% 1.39/0.54    inference(avatar_component_clause,[],[f149])).
% 1.39/0.54  fof(f188,plain,(
% 1.39/0.54    spl6_19 | spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_6),
% 1.39/0.54    inference(avatar_split_clause,[],[f122,f106,f84,f89,f94,f79,f185])).
% 1.39/0.54  fof(f106,plain,(
% 1.39/0.54    spl6_6 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.39/0.54  fof(f122,plain,(
% 1.39/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK2,sK0,sK1) | ~spl6_6),
% 1.39/0.54    inference(resolution,[],[f108,f44])).
% 1.39/0.54  fof(f44,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f21])).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f13])).
% 1.39/0.54  fof(f13,axiom,(
% 1.39/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 1.39/0.54  fof(f108,plain,(
% 1.39/0.54    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_6),
% 1.39/0.54    inference(avatar_component_clause,[],[f106])).
% 1.39/0.54  fof(f183,plain,(
% 1.39/0.54    spl6_18 | spl6_1 | ~spl6_4 | ~spl6_3 | ~spl6_2 | ~spl6_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f119,f101,f84,f89,f94,f79,f180])).
% 1.39/0.54  fof(f101,plain,(
% 1.39/0.54    spl6_5 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.39/0.54  fof(f119,plain,(
% 1.39/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_connsp_2(sK3,sK0,sK1) | ~spl6_5),
% 1.39/0.54    inference(resolution,[],[f103,f44])).
% 1.39/0.54  fof(f103,plain,(
% 1.39/0.54    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_5),
% 1.39/0.54    inference(avatar_component_clause,[],[f101])).
% 1.39/0.54  fof(f171,plain,(
% 1.39/0.54    spl6_10 | spl6_16 | ~spl6_6),
% 1.39/0.54    inference(avatar_split_clause,[],[f124,f106,f168,f132])).
% 1.39/0.54  fof(f132,plain,(
% 1.39/0.54    spl6_10 <=> v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.39/0.54  fof(f124,plain,(
% 1.39/0.54    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_6),
% 1.39/0.54    inference(resolution,[],[f108,f52])).
% 1.39/0.54  fof(f52,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f24,plain,(
% 1.39/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,axiom,(
% 1.39/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.39/0.54  fof(f158,plain,(
% 1.39/0.54    spl6_10 | spl6_14 | ~spl6_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f121,f101,f155,f132])).
% 1.39/0.54  fof(f121,plain,(
% 1.39/0.54    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_5),
% 1.39/0.54    inference(resolution,[],[f103,f52])).
% 1.39/0.54  fof(f152,plain,(
% 1.39/0.54    ~spl6_13 | spl6_12),
% 1.39/0.54    inference(avatar_split_clause,[],[f145,f141,f149])).
% 1.39/0.54  fof(f141,plain,(
% 1.39/0.54    spl6_12 <=> m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.39/0.54  fof(f145,plain,(
% 1.39/0.54    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_12),
% 1.39/0.54    inference(resolution,[],[f143,f53])).
% 1.39/0.54  fof(f53,plain,(
% 1.39/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f25])).
% 1.39/0.54  fof(f25,plain,(
% 1.39/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.39/0.54    inference(ennf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,axiom,(
% 1.39/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.39/0.54  fof(f143,plain,(
% 1.39/0.54    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl6_12),
% 1.39/0.54    inference(avatar_component_clause,[],[f141])).
% 1.39/0.54  fof(f144,plain,(
% 1.39/0.54    ~spl6_12),
% 1.39/0.54    inference(avatar_split_clause,[],[f66,f141])).
% 1.39/0.54  fof(f66,plain,(
% 1.39/0.54    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    inference(definition_unfolding,[],[f35,f48])).
% 1.39/0.54  fof(f35,plain,(
% 1.39/0.54    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.39/0.54    inference(flattening,[],[f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f15])).
% 1.39/0.54  fof(f15,negated_conjecture,(
% 1.39/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.39/0.54    inference(negated_conjecture,[],[f14])).
% 1.39/0.54  fof(f14,conjecture,(
% 1.39/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.39/0.54  fof(f139,plain,(
% 1.39/0.54    ~spl6_10 | spl6_11 | ~spl6_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f120,f101,f136,f132])).
% 1.39/0.54  fof(f120,plain,(
% 1.39/0.54    v1_xboole_0(sK3) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl6_5),
% 1.39/0.54    inference(resolution,[],[f103,f50])).
% 1.39/0.54  fof(f50,plain,(
% 1.39/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f24])).
% 1.39/0.54  fof(f109,plain,(
% 1.39/0.54    spl6_6),
% 1.39/0.54    inference(avatar_split_clause,[],[f36,f106])).
% 1.39/0.54  fof(f36,plain,(
% 1.39/0.54    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f104,plain,(
% 1.39/0.54    spl6_5),
% 1.39/0.54    inference(avatar_split_clause,[],[f34,f101])).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f97,plain,(
% 1.39/0.54    spl6_4),
% 1.39/0.54    inference(avatar_split_clause,[],[f37,f94])).
% 1.39/0.54  fof(f37,plain,(
% 1.39/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f92,plain,(
% 1.39/0.54    spl6_3),
% 1.39/0.54    inference(avatar_split_clause,[],[f40,f89])).
% 1.39/0.54  fof(f40,plain,(
% 1.39/0.54    l1_pre_topc(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f87,plain,(
% 1.39/0.54    spl6_2),
% 1.39/0.54    inference(avatar_split_clause,[],[f39,f84])).
% 1.39/0.54  fof(f39,plain,(
% 1.39/0.54    v2_pre_topc(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  fof(f82,plain,(
% 1.39/0.54    ~spl6_1),
% 1.39/0.54    inference(avatar_split_clause,[],[f38,f79])).
% 1.39/0.54  fof(f38,plain,(
% 1.39/0.54    ~v2_struct_0(sK0)),
% 1.39/0.54    inference(cnf_transformation,[],[f17])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (12197)------------------------------
% 1.39/0.54  % (12197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (12197)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (12197)Memory used [KB]: 11001
% 1.39/0.54  % (12197)Time elapsed: 0.097 s
% 1.39/0.54  % (12197)------------------------------
% 1.39/0.54  % (12197)------------------------------
% 1.39/0.54  % (12203)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.54  % (12174)Success in time 0.181 s
%------------------------------------------------------------------------------
