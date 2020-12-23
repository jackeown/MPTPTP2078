%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 205 expanded)
%              Number of leaves         :   20 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          :  381 ( 876 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f89,f98,f103,f108,f113,f121,f127])).

fof(f127,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f125,f97])).

fof(f97,plain,
    ( ~ r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_7
  <=> r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f125,plain,
    ( r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f124,f88])).

fof(f88,plain,
    ( k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_6
  <=> k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f124,plain,
    ( r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),a_2_0_yellow19(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f67,f62,f57,f52,f120,f43])).

fof(f43,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | r2_hidden(X3,a_2_0_yellow19(X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      | X0 != X3
      | ~ m1_connsp_2(X3,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ( sK3(X0,X1,X2) = X0
            & m1_connsp_2(sK3(X0,X1,X2),X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( X0 = X4
          & m1_connsp_2(X4,X1,X2) )
     => ( sK3(X0,X1,X2) = X0
        & m1_connsp_2(sK3(X0,X1,X2),X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X4] :
              ( X0 = X4
              & m1_connsp_2(X4,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
          | ! [X3] :
              ( X0 != X3
              | ~ m1_connsp_2(X3,X1,X2) ) )
        & ( ? [X3] :
              ( X0 = X3
              & m1_connsp_2(X3,X1,X2) )
          | ~ r2_hidden(X0,a_2_0_yellow19(X1,X2)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_yellow19(X1,X2))
      <=> ? [X3] :
            ( X0 = X3
            & m1_connsp_2(X3,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

fof(f120,plain,
    ( m1_connsp_2(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_11
  <=> m1_connsp_2(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f52,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f57,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f62,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f67,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f121,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f115,f110,f105,f100,f65,f60,f55,f50,f118])).

fof(f100,plain,
    ( spl4_8
  <=> r2_hidden(sK1,sK2(sK0,k1_yellow19(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f105,plain,
    ( spl4_9
  <=> v3_pre_topc(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f110,plain,
    ( spl4_10
  <=> m1_subset_1(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f115,plain,
    ( m1_connsp_2(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10 ),
    inference(unit_resulting_resolution,[],[f67,f62,f57,f52,f102,f107,f112,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f112,plain,
    ( m1_subset_1(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f107,plain,
    ( v3_pre_topc(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f102,plain,
    ( r2_hidden(sK1,sK2(sK0,k1_yellow19(sK0,sK1),sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f113,plain,
    ( spl4_10
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f90,f60,f55,f45,f110])).

fof(f45,plain,
    ( spl4_1
  <=> r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f90,plain,
    ( m1_subset_1(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f47,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(X2,sK2(X0,X1,X2))
              & v3_pre_topc(sK2(X0,X1,X2),X0)
              & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(X2,sK2(X0,X1,X2))
        & v3_pre_topc(sK2(X0,X1,X2),X0)
        & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f47,plain,
    ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f108,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f91,f60,f55,f45,f105])).

fof(f91,plain,
    ( v3_pre_topc(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f47,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK2(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f92,f60,f55,f45,f100])).

fof(f92,plain,
    ( r2_hidden(sK1,sK2(sK0,k1_yellow19(sK0,sK1),sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f47,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK2(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f98,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f93,f60,f55,f45,f95])).

fof(f93,plain,
    ( ~ r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f62,f57,f47,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f84,f65,f60,f55,f50,f86])).

fof(f84,plain,
    ( k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f67,f62,f57,f52,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).

fof(f68,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).

fof(f63,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f60])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f50])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f32,f45])).

fof(f32,plain,(
    ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:30:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (11860)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (11860)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (11867)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f48,f53,f58,f63,f68,f89,f98,f103,f108,f113,f121,f127])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | spl4_7 | ~spl4_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | spl4_7 | ~spl4_11)),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1)) | spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl4_7 <=> r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_6 | ~spl4_11)),
% 0.21/0.48    inference(forward_demodulation,[],[f124,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f86])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl4_6 <=> k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),a_2_0_yellow19(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_11)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f62,f57,f52,f120,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~m1_connsp_2(X3,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | r2_hidden(X3,a_2_0_yellow19(X1,X2))) )),
% 0.21/0.48    inference(equality_resolution,[],[f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_yellow19(X1,X2)) | X0 != X3 | ~m1_connsp_2(X3,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ! [X3] : (X0 != X3 | ~m1_connsp_2(X3,X1,X2))) & ((sK3(X0,X1,X2) = X0 & m1_connsp_2(sK3(X0,X1,X2),X1,X2)) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f25,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X4] : (X0 = X4 & m1_connsp_2(X4,X1,X2)) => (sK3(X0,X1,X2) = X0 & m1_connsp_2(sK3(X0,X1,X2),X1,X2)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ! [X3] : (X0 != X3 | ~m1_connsp_2(X3,X1,X2))) & (? [X4] : (X0 = X4 & m1_connsp_2(X4,X1,X2)) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(rectify,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_yellow19(X1,X2)) | ! [X3] : (X0 != X3 | ~m1_connsp_2(X3,X1,X2))) & (? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2)) | ~r2_hidden(X0,a_2_0_yellow19(X1,X2)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_yellow19(X1,X2)) <=> ? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_yellow19(X1,X2)) <=> ? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_yellow19(X1,X2)) <=> ? [X3] : (X0 = X3 & m1_connsp_2(X3,X1,X2))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    m1_connsp_2(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0,sK1) | ~spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f118])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    spl4_11 <=> m1_connsp_2(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    spl4_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_3 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl4_4 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ~v2_struct_0(sK0) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl4_5 <=> v2_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    spl4_11 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_8 | ~spl4_9 | ~spl4_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f115,f110,f105,f100,f65,f60,f55,f50,f118])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_8 <=> r2_hidden(sK1,sK2(sK0,k1_yellow19(sK0,sK1),sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl4_9 <=> v3_pre_topc(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    spl4_10 <=> m1_subset_1(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    m1_connsp_2(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_8 | ~spl4_9 | ~spl4_10)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f62,f57,f52,f102,f107,f112,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X1,X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f110])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    v3_pre_topc(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f105])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    r2_hidden(sK1,sK2(sK0,k1_yellow19(sK0,sK1),sK1)) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl4_10 | spl4_1 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f90,f60,f55,f45,f110])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl4_1 <=> r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    m1_subset_1(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f57,f47,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(X2,sK2(X0,X1,X2)) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(X2,sK2(X0,X1,X2)) & v3_pre_topc(sK2(X0,X1,X2),X0) & m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(rectify,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ~r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl4_9 | spl4_1 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f91,f60,f55,f45,f105])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    v3_pre_topc(sK2(sK0,k1_yellow19(sK0,sK1),sK1),sK0) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f57,f47,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v3_pre_topc(sK2(X0,X1,X2),X0) | r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl4_8 | spl4_1 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f92,f60,f55,f45,f100])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    r2_hidden(sK1,sK2(sK0,k1_yellow19(sK0,sK1),sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f57,f47,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(X2,sK2(X0,X1,X2)) | r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~spl4_7 | spl4_1 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f93,f60,f55,f45,f95])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~r2_hidden(sK2(sK0,k1_yellow19(sK0,sK1),sK1),k1_yellow19(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f62,f57,f47,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl4_6 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f84,f65,f60,f55,f50,f86])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    k1_yellow19(sK0,sK1) = a_2_0_yellow19(sK0,sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f67,f62,f57,f52,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_yellow19(X0,X1) = a_2_0_yellow19(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~spl4_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f65])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    (~r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f18,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r2_waybel_7(sK0,k1_yellow19(sK0,X1),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X1] : (~r2_waybel_7(sK0,k1_yellow19(sK0,X1),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (~r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_waybel_7(X0,k1_yellow19(X0,X1),X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_waybel_7(X0,k1_yellow19(X0,X1),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f60])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f55])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f50])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f45])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ~r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (11860)------------------------------
% 0.21/0.48  % (11860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (11860)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (11860)Memory used [KB]: 6140
% 0.21/0.48  % (11860)Time elapsed: 0.064 s
% 0.21/0.48  % (11860)------------------------------
% 0.21/0.48  % (11860)------------------------------
% 0.21/0.48  % (11850)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.48  % (11845)Success in time 0.122 s
%------------------------------------------------------------------------------
