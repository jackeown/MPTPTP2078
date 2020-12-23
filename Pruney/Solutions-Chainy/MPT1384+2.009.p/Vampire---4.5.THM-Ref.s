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
% DateTime   : Thu Dec  3 13:15:07 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   97 (1164 expanded)
%              Number of leaves         :   17 ( 271 expanded)
%              Depth                    :   16
%              Number of atoms          :  367 (6884 expanded)
%              Number of equality atoms :   11 ( 102 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (21329)Termination reason: Refutation not found, incomplete strategy

fof(f687,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f105,f109,f144,f182,f218,f514,f686])).

fof(f686,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f55,f658,f32,f181])).

fof(f181,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_10
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f658,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f35,f33,f34,f86,f81,f32,f104,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f104,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl6_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f81,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f86,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f514,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | spl6_1
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f194,f284,f411,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f411,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))))
    | spl6_1
    | ~ spl6_7
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f33,f34,f35,f192,f233,f212,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f212,plain,
    ( m1_connsp_2(sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))
    | spl6_1
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f193,f192,f143])).

fof(f143,plain,
    ( ! [X2] :
        ( m1_connsp_2(sK3(X2),sK0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl6_7
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f193,plain,
    ( r2_hidden(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f91,f32,f175,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f175,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f174,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f174,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f135,f110])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0,u1_struct_0(sK0)),sK1)
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f73,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0] :
      ( r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f135,plain,(
    ! [X0] :
      ( r2_hidden(sK4(k1_tops_1(sK0,sK1),X0),sK1)
      | r1_tarski(k1_tops_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f65,f38])).

fof(f65,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f35,f32,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f91,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f65,f88,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f34,f35,f35,f32,f32,f82,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k1_tops_1(X0,X2) != X2
      | v3_pre_topc(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f82,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f233,plain,
    ( m1_subset_1(sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_1
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f193,f192,f217])).

fof(f217,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl6_11
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f192,plain,
    ( m1_subset_1(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f91,f32,f175,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK5(X0,X1,X2),X0)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f284,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(unit_resulting_resolution,[],[f35,f32,f213,f233,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f213,plain,
    ( r1_tarski(sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1)
    | spl6_1
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f193,f192,f108])).

fof(f108,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_4
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f194,plain,
    ( ~ r2_hidden(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1))
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f91,f32,f175,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f218,plain,
    ( spl6_1
    | spl6_11 ),
    inference(avatar_split_clause,[],[f26,f216,f80])).

fof(f26,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f182,plain,
    ( ~ spl6_1
    | spl6_10 ),
    inference(avatar_split_clause,[],[f29,f180,f80])).

fof(f29,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f144,plain,
    ( spl6_1
    | spl6_7 ),
    inference(avatar_split_clause,[],[f27,f142,f80])).

fof(f27,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,
    ( spl6_1
    | spl6_4 ),
    inference(avatar_split_clause,[],[f28,f107,f80])).

fof(f28,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f105,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f30,f102,f80])).

fof(f30,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f31,f84,f80])).

fof(f31,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (21313)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (21333)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.53  % (21321)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.30/0.53  % (21325)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.30/0.53  % (21311)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (21330)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.54  % (21316)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.54  % (21322)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.30/0.54  % (21330)Refutation not found, incomplete strategy% (21330)------------------------------
% 1.30/0.54  % (21330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (21309)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.54  % (21315)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.30/0.54  % (21330)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (21330)Memory used [KB]: 1791
% 1.30/0.54  % (21330)Time elapsed: 0.081 s
% 1.30/0.54  % (21330)------------------------------
% 1.30/0.54  % (21330)------------------------------
% 1.30/0.54  % (21329)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.30/0.54  % (21328)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.30/0.54  % (21317)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.30/0.54  % (21310)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.30/0.54  % (21338)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.46/0.54  % (21312)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.46/0.54  % (21314)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.46/0.54  % (21334)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.46/0.55  % (21326)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.55  % (21336)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.55  % (21332)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.46/0.55  % (21331)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.46/0.56  % (21320)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.46/0.56  % (21318)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.56  % (21329)Refutation not found, incomplete strategy% (21329)------------------------------
% 1.46/0.56  % (21329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (21323)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.56  % (21319)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.56  % (21324)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.46/0.57  % (21313)Refutation found. Thanks to Tanya!
% 1.46/0.57  % SZS status Theorem for theBenchmark
% 1.46/0.57  % SZS output start Proof for theBenchmark
% 1.46/0.57  % (21329)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  fof(f687,plain,(
% 1.46/0.57    $false),
% 1.46/0.57    inference(avatar_sat_refutation,[],[f87,f105,f109,f144,f182,f218,f514,f686])).
% 1.46/0.57  fof(f686,plain,(
% 1.46/0.57    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_10),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f684])).
% 1.46/0.57  fof(f684,plain,(
% 1.46/0.57    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_10)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f55,f658,f32,f181])).
% 1.46/0.57  fof(f181,plain,(
% 1.46/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl6_10),
% 1.46/0.57    inference(avatar_component_clause,[],[f180])).
% 1.46/0.57  fof(f180,plain,(
% 1.46/0.57    spl6_10 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.46/0.57  fof(f32,plain,(
% 1.46/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f13,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f12])).
% 1.46/0.57  fof(f12,plain,(
% 1.46/0.57    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f11])).
% 1.46/0.57  fof(f11,negated_conjecture,(
% 1.46/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.46/0.57    inference(negated_conjecture,[],[f10])).
% 1.46/0.57  fof(f10,conjecture,(
% 1.46/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_connsp_2)).
% 1.46/0.57  fof(f658,plain,(
% 1.46/0.57    m1_connsp_2(sK1,sK0,sK2) | (~spl6_1 | ~spl6_2 | ~spl6_3)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f35,f33,f34,f86,f81,f32,f104,f46])).
% 1.46/0.57  fof(f46,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f21])).
% 1.46/0.57  fof(f21,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f20])).
% 1.46/0.57  fof(f20,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f9])).
% 1.46/0.57  fof(f9,axiom,(
% 1.46/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.46/0.57  fof(f104,plain,(
% 1.46/0.57    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_3),
% 1.46/0.57    inference(avatar_component_clause,[],[f102])).
% 1.46/0.57  fof(f102,plain,(
% 1.46/0.57    spl6_3 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.46/0.57  fof(f81,plain,(
% 1.46/0.57    v3_pre_topc(sK1,sK0) | ~spl6_1),
% 1.46/0.57    inference(avatar_component_clause,[],[f80])).
% 1.46/0.57  fof(f80,plain,(
% 1.46/0.57    spl6_1 <=> v3_pre_topc(sK1,sK0)),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.46/0.57  fof(f86,plain,(
% 1.46/0.57    r2_hidden(sK2,sK1) | ~spl6_2),
% 1.46/0.57    inference(avatar_component_clause,[],[f84])).
% 1.46/0.57  fof(f84,plain,(
% 1.46/0.57    spl6_2 <=> r2_hidden(sK2,sK1)),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.46/0.57  fof(f34,plain,(
% 1.46/0.57    v2_pre_topc(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f33,plain,(
% 1.46/0.57    ~v2_struct_0(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f35,plain,(
% 1.46/0.57    l1_pre_topc(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f55,plain,(
% 1.46/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.46/0.57    inference(equality_resolution,[],[f51])).
% 1.46/0.57  fof(f51,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.46/0.57    inference(cnf_transformation,[],[f2])).
% 1.46/0.57  fof(f2,axiom,(
% 1.46/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.46/0.57  fof(f514,plain,(
% 1.46/0.57    spl6_1 | ~spl6_4 | ~spl6_7 | ~spl6_11),
% 1.46/0.57    inference(avatar_contradiction_clause,[],[f508])).
% 1.46/0.57  fof(f508,plain,(
% 1.46/0.57    $false | (spl6_1 | ~spl6_4 | ~spl6_7 | ~spl6_11)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f194,f284,f411,f38])).
% 1.46/0.57  fof(f38,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f14])).
% 1.46/0.57  fof(f14,plain,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f1])).
% 1.46/0.57  fof(f1,axiom,(
% 1.46/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.46/0.57  fof(f411,plain,(
% 1.46/0.57    r2_hidden(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))))) | (spl6_1 | ~spl6_7 | ~spl6_11)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f33,f34,f35,f192,f233,f212,f48])).
% 1.46/0.57  fof(f48,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.46/0.57    inference(flattening,[],[f22])).
% 1.46/0.57  fof(f22,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f8])).
% 1.46/0.57  fof(f8,axiom,(
% 1.46/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.46/0.57  fof(f212,plain,(
% 1.46/0.57    m1_connsp_2(sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK0,sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) | (spl6_1 | ~spl6_7)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f193,f192,f143])).
% 1.46/0.57  fof(f143,plain,(
% 1.46/0.57    ( ! [X2] : (m1_connsp_2(sK3(X2),sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) ) | ~spl6_7),
% 1.46/0.57    inference(avatar_component_clause,[],[f142])).
% 1.46/0.57  fof(f142,plain,(
% 1.46/0.57    spl6_7 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.46/0.57  fof(f193,plain,(
% 1.46/0.57    r2_hidden(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1) | spl6_1),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f91,f32,f175,f42])).
% 1.46/0.57  fof(f42,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK5(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f16])).
% 1.46/0.57  fof(f16,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.46/0.57    inference(flattening,[],[f15])).
% 1.46/0.57  fof(f15,plain,(
% 1.46/0.57    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f3])).
% 1.46/0.57  fof(f3,axiom,(
% 1.46/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 1.46/0.57  fof(f175,plain,(
% 1.46/0.57    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f174,f36])).
% 1.46/0.57  fof(f36,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f4])).
% 1.46/0.57  fof(f4,axiom,(
% 1.46/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.46/0.57  fof(f174,plain,(
% 1.46/0.57    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.46/0.57    inference(duplicate_literal_removal,[],[f171])).
% 1.46/0.57  fof(f171,plain,(
% 1.46/0.57    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.46/0.57    inference(resolution,[],[f135,f110])).
% 1.46/0.57  fof(f110,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(sK4(X0,u1_struct_0(sK0)),sK1) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 1.46/0.57    inference(resolution,[],[f73,f40])).
% 1.46/0.57  fof(f40,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f14])).
% 1.46/0.57  fof(f73,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.46/0.57    inference(resolution,[],[f66,f38])).
% 1.46/0.57  fof(f66,plain,(
% 1.46/0.57    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f32,f37])).
% 1.46/0.57  fof(f37,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f4])).
% 1.46/0.57  fof(f135,plain,(
% 1.46/0.57    ( ! [X0] : (r2_hidden(sK4(k1_tops_1(sK0,sK1),X0),sK1) | r1_tarski(k1_tops_1(sK0,sK1),X0)) )),
% 1.46/0.57    inference(resolution,[],[f77,f39])).
% 1.46/0.57  fof(f39,plain,(
% 1.46/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f14])).
% 1.46/0.57  fof(f77,plain,(
% 1.46/0.57    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | r2_hidden(X0,sK1)) )),
% 1.46/0.57    inference(resolution,[],[f65,f38])).
% 1.46/0.57  fof(f65,plain,(
% 1.46/0.57    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f35,f32,f45])).
% 1.46/0.57  fof(f45,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f19])).
% 1.46/0.57  fof(f19,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.46/0.57    inference(ennf_transformation,[],[f5])).
% 1.46/0.57  fof(f5,axiom,(
% 1.46/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 1.46/0.57  fof(f91,plain,(
% 1.46/0.57    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl6_1),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f65,f88,f53])).
% 1.46/0.57  fof(f53,plain,(
% 1.46/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.46/0.57    inference(cnf_transformation,[],[f2])).
% 1.46/0.57  fof(f88,plain,(
% 1.46/0.57    sK1 != k1_tops_1(sK0,sK1) | spl6_1),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f34,f35,f35,f32,f32,f82,f49])).
% 1.46/0.57  fof(f49,plain,(
% 1.46/0.57    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k1_tops_1(X0,X2) != X2 | v3_pre_topc(X2,X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f25])).
% 1.46/0.57  fof(f25,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.46/0.57    inference(flattening,[],[f24])).
% 1.46/0.57  fof(f24,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.46/0.57    inference(ennf_transformation,[],[f7])).
% 1.46/0.57  fof(f7,axiom,(
% 1.46/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 1.46/0.57  fof(f82,plain,(
% 1.46/0.57    ~v3_pre_topc(sK1,sK0) | spl6_1),
% 1.46/0.57    inference(avatar_component_clause,[],[f80])).
% 1.46/0.57  fof(f233,plain,(
% 1.46/0.57    m1_subset_1(sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),k1_zfmisc_1(u1_struct_0(sK0))) | (spl6_1 | ~spl6_11)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f193,f192,f217])).
% 1.46/0.57  fof(f217,plain,(
% 1.46/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1)) ) | ~spl6_11),
% 1.46/0.57    inference(avatar_component_clause,[],[f216])).
% 1.46/0.57  fof(f216,plain,(
% 1.46/0.57    spl6_11 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.46/0.57  fof(f192,plain,(
% 1.46/0.57    m1_subset_1(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | spl6_1),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f91,f32,f175,f41])).
% 1.46/0.57  fof(f41,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK5(X0,X1,X2),X0) | r1_tarski(X1,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f16])).
% 1.46/0.57  fof(f284,plain,(
% 1.46/0.57    r1_tarski(k1_tops_1(sK0,sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)))),k1_tops_1(sK0,sK1)) | (spl6_1 | ~spl6_4 | ~spl6_11)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f35,f32,f213,f233,f44])).
% 1.46/0.57  fof(f44,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 1.46/0.57    inference(cnf_transformation,[],[f18])).
% 1.46/0.57  fof(f18,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.46/0.57    inference(flattening,[],[f17])).
% 1.46/0.57  fof(f17,plain,(
% 1.46/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.46/0.57    inference(ennf_transformation,[],[f6])).
% 1.46/0.57  fof(f6,axiom,(
% 1.46/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.46/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 1.46/0.57  fof(f213,plain,(
% 1.46/0.57    r1_tarski(sK3(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),sK1) | (spl6_1 | ~spl6_4)),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f193,f192,f108])).
% 1.46/0.57  fof(f108,plain,(
% 1.46/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1)) ) | ~spl6_4),
% 1.46/0.57    inference(avatar_component_clause,[],[f107])).
% 1.46/0.57  fof(f107,plain,(
% 1.46/0.57    spl6_4 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.46/0.57  fof(f194,plain,(
% 1.46/0.57    ~r2_hidden(sK5(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) | spl6_1),
% 1.46/0.57    inference(unit_resulting_resolution,[],[f91,f32,f175,f43])).
% 1.46/0.57  fof(f43,plain,(
% 1.46/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2) | r1_tarski(X1,X2)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f16])).
% 1.46/0.57  fof(f218,plain,(
% 1.46/0.57    spl6_1 | spl6_11),
% 1.46/0.57    inference(avatar_split_clause,[],[f26,f216,f80])).
% 1.46/0.57  fof(f26,plain,(
% 1.46/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f182,plain,(
% 1.46/0.57    ~spl6_1 | spl6_10),
% 1.46/0.57    inference(avatar_split_clause,[],[f29,f180,f80])).
% 1.46/0.57  fof(f29,plain,(
% 1.46/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f144,plain,(
% 1.46/0.57    spl6_1 | spl6_7),
% 1.46/0.57    inference(avatar_split_clause,[],[f27,f142,f80])).
% 1.46/0.57  fof(f27,plain,(
% 1.46/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f109,plain,(
% 1.46/0.57    spl6_1 | spl6_4),
% 1.46/0.57    inference(avatar_split_clause,[],[f28,f107,f80])).
% 1.46/0.57  fof(f28,plain,(
% 1.46/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f105,plain,(
% 1.46/0.57    ~spl6_1 | spl6_3),
% 1.46/0.57    inference(avatar_split_clause,[],[f30,f102,f80])).
% 1.46/0.57  fof(f30,plain,(
% 1.46/0.57    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  fof(f87,plain,(
% 1.46/0.57    ~spl6_1 | spl6_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f31,f84,f80])).
% 1.46/0.57  fof(f31,plain,(
% 1.46/0.57    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f13])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (21313)------------------------------
% 1.46/0.57  % (21313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (21313)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (21313)Memory used [KB]: 6652
% 1.46/0.57  % (21313)Time elapsed: 0.159 s
% 1.46/0.57  % (21313)------------------------------
% 1.46/0.57  % (21313)------------------------------
% 1.46/0.57  % (21329)Memory used [KB]: 10746
% 1.46/0.57  % (21329)Time elapsed: 0.141 s
% 1.46/0.57  % (21329)------------------------------
% 1.46/0.57  % (21329)------------------------------
% 1.46/0.57  % (21337)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.57  % (21308)Success in time 0.202 s
%------------------------------------------------------------------------------
