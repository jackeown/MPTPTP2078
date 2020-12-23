%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 465 expanded)
%              Number of leaves         :   36 ( 224 expanded)
%              Depth                    :   11
%              Number of atoms          :  792 (4394 expanded)
%              Number of equality atoms :   26 ( 364 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1070,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f505,f509,f525,f558,f610,f683,f688,f693,f698,f704,f707,f715,f719,f723,f728,f733,f738,f753,f973,f980,f1065])).

fof(f1065,plain,
    ( ~ spl8_68
    | spl8_146
    | ~ spl8_147 ),
    inference(avatar_contradiction_clause,[],[f1061])).

fof(f1061,plain,
    ( $false
    | ~ spl8_68
    | spl8_146
    | ~ spl8_147 ),
    inference(unit_resulting_resolution,[],[f44,f45,f46,f48,f49,f50,f51,f47,f52,f504,f972,f979,f76])).

fof(f76,plain,(
    ! [X6,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X6,X2,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k10_yellow_6(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X2))
                        & m1_connsp_2(sK6(X0,X1,X2),X0,sK5(X0,X1,X2)) )
                      | ~ r2_hidden(sK5(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK5(X0,X1,X2)) )
                      | r2_hidden(sK5(X0,X1,X2),X2) )
                    & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X6))
                            & m1_connsp_2(sK7(X0,X1,X6),X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ? [X4] :
                ( ~ r1_waybel_0(X0,X1,X4)
                & m1_connsp_2(X4,X0,X3) )
            | ~ r2_hidden(X3,X2) )
          & ( ! [X5] :
                ( r1_waybel_0(X0,X1,X5)
                | ~ m1_connsp_2(X5,X0,X3) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ? [X4] :
              ( ~ r1_waybel_0(X0,X1,X4)
              & m1_connsp_2(X4,X0,sK5(X0,X1,X2)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK5(X0,X1,X2)) )
          | r2_hidden(sK5(X0,X1,X2),X2) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK5(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X2))
        & m1_connsp_2(sK6(X0,X1,X2),X0,sK5(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK7(X0,X1,X6))
        & m1_connsp_2(sK7(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

% (13330)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X5] :
                            ( r1_waybel_0(X0,X1,X5)
                            | ~ m1_connsp_2(X5,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ? [X7] :
                              ( ~ r1_waybel_0(X0,X1,X7)
                              & m1_connsp_2(X7,X0,X6) ) )
                        & ( ! [X8] :
                              ( r1_waybel_0(X0,X1,X8)
                              | ~ m1_connsp_2(X8,X0,X6) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ? [X3] :
                      ( ( ? [X4] :
                            ( ~ r1_waybel_0(X0,X1,X4)
                            & m1_connsp_2(X4,X0,X3) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ! [X4] :
                            ( r1_waybel_0(X0,X1,X4)
                            | ~ m1_connsp_2(X4,X0,X3) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ? [X4] :
                              ( ~ r1_waybel_0(X0,X1,X4)
                              & m1_connsp_2(X4,X0,X3) ) )
                        & ( ! [X4] :
                              ( r1_waybel_0(X0,X1,X4)
                              | ~ m1_connsp_2(X4,X0,X3) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k10_yellow_6(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f979,plain,
    ( m1_connsp_2(sK4(sK0,sK3,sK1),sK0,sK1)
    | ~ spl8_147 ),
    inference(avatar_component_clause,[],[f977])).

fof(f977,plain,
    ( spl8_147
  <=> m1_connsp_2(sK4(sK0,sK3,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).

fof(f972,plain,
    ( ~ r1_waybel_0(sK0,sK2,sK4(sK0,sK3,sK1))
    | spl8_146 ),
    inference(avatar_component_clause,[],[f970])).

fof(f970,plain,
    ( spl8_146
  <=> r1_waybel_0(sK0,sK2,sK4(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).

fof(f504,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl8_68
  <=> m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f52,plain,(
    r2_hidden(sK1,k10_yellow_6(sK0,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3))
    & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & r2_hidden(sK1,k10_yellow_6(sK0,sK2))
    & l1_waybel_0(sK2,sK0)
    & v7_waybel_0(sK2)
    & v4_orders_2(sK2)
    & ~ v2_struct_0(sK2)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                    & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r2_hidden(X1,k10_yellow_6(X0,X2))
                & l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(sK0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & r2_hidden(X1,k10_yellow_6(sK0,X2))
              & l1_waybel_0(X2,sK0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_hidden(X1,k2_pre_topc(sK0,X3))
                & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & r2_hidden(X1,k10_yellow_6(sK0,X2))
            & l1_waybel_0(X2,sK0)
            & v7_waybel_0(X2)
            & v4_orders_2(X2)
            & ~ v2_struct_0(X2) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(sK1,k2_pre_topc(sK0,X3))
              & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & r2_hidden(sK1,k10_yellow_6(sK0,X2))
          & l1_waybel_0(X2,sK0)
          & v7_waybel_0(X2)
          & v4_orders_2(X2)
          & ~ v2_struct_0(X2) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r2_hidden(sK1,k2_pre_topc(sK0,X3))
            & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & r2_hidden(sK1,k10_yellow_6(sK0,X2))
        & l1_waybel_0(X2,sK0)
        & v7_waybel_0(X2)
        & v4_orders_2(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(sK1,k2_pre_topc(sK0,X3))
          & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & r2_hidden(sK1,k10_yellow_6(sK0,sK2))
      & l1_waybel_0(sK2,sK0)
      & v7_waybel_0(sK2)
      & v4_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ~ r2_hidden(sK1,k2_pre_topc(sK0,X3))
        & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3))
      & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(X1,k2_pre_topc(X0,X3))
                  & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & r2_hidden(X1,k10_yellow_6(X0,X2))
              & l1_waybel_0(X2,X0)
              & v7_waybel_0(X2)
              & v4_orders_2(X2)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r2_hidden(X1,k10_yellow_6(X0,X2))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                       => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( l1_waybel_0(X2,X0)
                & v7_waybel_0(X2)
                & v4_orders_2(X2)
                & ~ v2_struct_0(X2) )
             => ( r2_hidden(X1,k10_yellow_6(X0,X2))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3
                     => r2_hidden(X1,k2_pre_topc(X0,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_9)).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    l1_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v7_waybel_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f980,plain,
    ( ~ spl8_104
    | spl8_147
    | ~ spl8_102
    | ~ spl8_78
    | ~ spl8_103 ),
    inference(avatar_split_clause,[],[f974,f685,f556,f680,f977,f690])).

fof(f690,plain,
    ( spl8_104
  <=> r2_hidden(sK1,sK4(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f680,plain,
    ( spl8_102
  <=> m1_subset_1(sK4(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f556,plain,
    ( spl8_78
  <=> ! [X6] :
        ( m1_connsp_2(X6,sK0,sK1)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X6,sK0)
        | ~ r2_hidden(sK1,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f685,plain,
    ( spl8_103
  <=> v3_pre_topc(sK4(sK0,sK3,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f974,plain,
    ( ~ m1_subset_1(sK4(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_connsp_2(sK4(sK0,sK3,sK1),sK0,sK1)
    | ~ r2_hidden(sK1,sK4(sK0,sK3,sK1))
    | ~ spl8_78
    | ~ spl8_103 ),
    inference(resolution,[],[f557,f687])).

fof(f687,plain,
    ( v3_pre_topc(sK4(sK0,sK3,sK1),sK0)
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f685])).

fof(f557,plain,
    ( ! [X6] :
        ( ~ v3_pre_topc(X6,sK0)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X6,sK0,sK1)
        | ~ r2_hidden(sK1,X6) )
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f556])).

fof(f973,plain,
    ( ~ spl8_146
    | ~ spl8_106
    | ~ spl8_69
    | ~ spl8_105 ),
    inference(avatar_split_clause,[],[f968,f695,f507,f701,f970])).

fof(f701,plain,
    ( spl8_106
  <=> r1_waybel_0(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f507,plain,
    ( spl8_69
  <=> ! [X5,X6] :
        ( ~ r1_xboole_0(X5,X6)
        | ~ r1_waybel_0(sK0,sK2,X5)
        | ~ r1_waybel_0(sK0,sK2,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).

fof(f695,plain,
    ( spl8_105
  <=> r1_xboole_0(sK3,sK4(sK0,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f968,plain,
    ( ~ r1_waybel_0(sK0,sK2,sK3)
    | ~ r1_waybel_0(sK0,sK2,sK4(sK0,sK3,sK1))
    | ~ spl8_69
    | ~ spl8_105 ),
    inference(resolution,[],[f508,f697])).

fof(f697,plain,
    ( r1_xboole_0(sK3,sK4(sK0,sK3,sK1))
    | ~ spl8_105 ),
    inference(avatar_component_clause,[],[f695])).

fof(f508,plain,
    ( ! [X6,X5] :
        ( ~ r1_xboole_0(X5,X6)
        | ~ r1_waybel_0(sK0,sK2,X5)
        | ~ r1_waybel_0(sK0,sK2,X6) )
    | ~ spl8_69 ),
    inference(avatar_component_clause,[],[f507])).

fof(f753,plain,(
    spl8_101 ),
    inference(avatar_contradiction_clause,[],[f749])).

fof(f749,plain,
    ( $false
    | spl8_101 ),
    inference(unit_resulting_resolution,[],[f53,f678])).

fof(f678,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_101 ),
    inference(avatar_component_clause,[],[f676])).

fof(f676,plain,
    ( spl8_101
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f738,plain,(
    spl8_83 ),
    inference(avatar_contradiction_clause,[],[f734])).

fof(f734,plain,
    ( $false
    | spl8_83 ),
    inference(unit_resulting_resolution,[],[f47,f586])).

fof(f586,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl8_83 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl8_83
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f733,plain,(
    spl8_82 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | spl8_82 ),
    inference(unit_resulting_resolution,[],[f51,f582])).

fof(f582,plain,
    ( ~ l1_waybel_0(sK2,sK0)
    | spl8_82 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl8_82
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f728,plain,(
    ~ spl8_62 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f48,f442])).

fof(f442,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl8_62
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f723,plain,(
    spl8_41 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | spl8_41 ),
    inference(unit_resulting_resolution,[],[f50,f349])).

fof(f349,plain,
    ( ~ v7_waybel_0(sK2)
    | spl8_41 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl8_41
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f719,plain,(
    spl8_40 ),
    inference(avatar_contradiction_clause,[],[f716])).

fof(f716,plain,
    ( $false
    | spl8_40 ),
    inference(unit_resulting_resolution,[],[f49,f345])).

fof(f345,plain,
    ( ~ v4_orders_2(sK2)
    | spl8_40 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl8_40
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f715,plain,(
    ~ spl8_31 ),
    inference(avatar_contradiction_clause,[],[f712])).

fof(f712,plain,
    ( $false
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f44,f240])).

fof(f240,plain,
    ( v2_struct_0(sK0)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl8_31
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f707,plain,(
    spl8_18 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl8_18 ),
    inference(unit_resulting_resolution,[],[f46,f174,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f174,plain,
    ( ~ l1_struct_0(sK0)
    | spl8_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl8_18
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f704,plain,
    ( spl8_31
    | ~ spl8_18
    | spl8_62
    | ~ spl8_82
    | spl8_106 ),
    inference(avatar_split_clause,[],[f699,f701,f580,f440,f172,f238])).

fof(f699,plain,
    ( r1_waybel_0(sK0,sK2,sK3)
    | ~ l1_waybel_0(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f68,f54])).

fof(f54,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3 ),
    inference(cnf_transformation,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f698,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_101
    | ~ spl8_83
    | spl8_105 ),
    inference(avatar_split_clause,[],[f674,f695,f584,f676,f108,f104,f238])).

fof(f104,plain,
    ( spl8_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f108,plain,
    ( spl8_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f674,plain,
    ( r1_xboole_0(sK3,sK4(sK0,sK3,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r1_xboole_0(X1,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ( r1_xboole_0(X1,sK4(X0,X1,X2))
                    & r2_hidden(X2,sK4(X0,X1,X2))
                    & v3_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_xboole_0(X1,X3)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK4(X0,X1,X2))
        & r2_hidden(X2,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X4] :
                      ( ~ r1_xboole_0(X1,X4)
                      | ~ r2_hidden(X2,X4)
                      | ~ v3_pre_topc(X4,X0)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
                  | ? [X3] :
                      ( r1_xboole_0(X1,X3)
                      & r2_hidden(X2,X3)
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ! [X3] :
                      ( ~ r1_xboole_0(X1,X3)
                      | ~ r2_hidden(X2,X3)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

fof(f55,plain,(
    ~ r2_hidden(sK1,k2_pre_topc(sK0,sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f693,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_101
    | ~ spl8_83
    | spl8_104 ),
    inference(avatar_split_clause,[],[f673,f690,f584,f676,f108,f104,f238])).

fof(f673,plain,
    ( r2_hidden(sK1,sK4(sK0,sK3,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | r2_hidden(X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f688,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_101
    | ~ spl8_83
    | spl8_103 ),
    inference(avatar_split_clause,[],[f672,f685,f584,f676,f108,f104,f238])).

fof(f672,plain,
    ( v3_pre_topc(sK4(sK0,sK3,sK1),sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f683,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_101
    | ~ spl8_83
    | spl8_102 ),
    inference(avatar_split_clause,[],[f671,f680,f584,f676,f108,f104,f238])).

fof(f671,plain,
    ( m1_subset_1(sK4(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f55,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_pre_topc(X0,X1))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f610,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f607])).

fof(f607,plain,
    ( $false
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f46,f110])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f558,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_2
    | spl8_78 ),
    inference(avatar_split_clause,[],[f531,f556,f108,f104,f238])).

fof(f531,plain,(
    ! [X6] :
      ( m1_connsp_2(X6,sK0,sK1)
      | ~ r2_hidden(sK1,X6)
      | ~ v3_pre_topc(X6,sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f525,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f45,f106])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f509,plain,
    ( spl8_31
    | ~ spl8_18
    | spl8_62
    | ~ spl8_40
    | ~ spl8_41
    | spl8_69 ),
    inference(avatar_split_clause,[],[f476,f507,f347,f343,f440,f172,f238])).

fof(f476,plain,(
    ! [X6,X5] :
      ( ~ r1_xboole_0(X5,X6)
      | ~ r1_waybel_0(sK0,sK2,X6)
      | ~ r1_waybel_0(sK0,sK2,X5)
      | ~ v7_waybel_0(sK2)
      | ~ v4_orders_2(sK2)
      | v2_struct_0(sK2)
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f51,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ~ r1_xboole_0(X2,X3)
              | ~ r1_waybel_0(X0,X1,X3)
              | ~ r1_waybel_0(X0,X1,X2) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_6)).

fof(f505,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_2
    | spl8_62
    | ~ spl8_40
    | ~ spl8_41
    | spl8_68 ),
    inference(avatar_split_clause,[],[f475,f502,f347,f343,f440,f108,f104,f238])).

fof(f475,plain,
    ( m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v7_waybel_0(sK2)
    | ~ v4_orders_2(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (13348)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (13332)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (13342)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (13338)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (13348)Refutation not found, incomplete strategy% (13348)------------------------------
% 0.21/0.47  % (13348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13348)Memory used [KB]: 10618
% 0.21/0.47  % (13348)Time elapsed: 0.068 s
% 0.21/0.47  % (13348)------------------------------
% 0.21/0.47  % (13348)------------------------------
% 0.21/0.47  % (13333)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (13338)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (13346)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (13328)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (13336)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (13335)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (13343)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (13339)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (13341)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (13334)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (13331)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f1070,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f505,f509,f525,f558,f610,f683,f688,f693,f698,f704,f707,f715,f719,f723,f728,f733,f738,f753,f973,f980,f1065])).
% 0.21/0.50  fof(f1065,plain,(
% 0.21/0.50    ~spl8_68 | spl8_146 | ~spl8_147),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f1061])).
% 0.21/0.50  fof(f1061,plain,(
% 0.21/0.50    $false | (~spl8_68 | spl8_146 | ~spl8_147)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f45,f46,f48,f49,f50,f51,f47,f52,f504,f972,f979,f76])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X6,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,k10_yellow_6(X0,X1)) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X8,X1] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X0)) | k10_yellow_6(X0,X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | (((~r1_waybel_0(X0,X1,sK6(X0,X1,X2)) & m1_connsp_2(sK6(X0,X1,X2),X0,sK5(X0,X1,X2))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK5(X0,X1,X2))) | r2_hidden(sK5(X0,X1,X2),X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | (~r1_waybel_0(X0,X1,sK7(X0,X1,X6)) & m1_connsp_2(sK7(X0,X1,X6),X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f39,f42,f41,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0))) => ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK5(X0,X1,X2))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,sK5(X0,X1,X2))) | r2_hidden(sK5(X0,X1,X2),X2)) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,sK5(X0,X1,X2))) => (~r1_waybel_0(X0,X1,sK6(X0,X1,X2)) & m1_connsp_2(sK6(X0,X1,X2),X0,sK5(X0,X1,X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X6,X1,X0] : (? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6)) => (~r1_waybel_0(X0,X1,sK7(X0,X1,X6)) & m1_connsp_2(sK7(X0,X1,X6),X0,X6)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  % (13330)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X5] : (r1_waybel_0(X0,X1,X5) | ~m1_connsp_2(X5,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X6] : (((r2_hidden(X6,X2) | ? [X7] : (~r1_waybel_0(X0,X1,X7) & m1_connsp_2(X7,X0,X6))) & (! [X8] : (r1_waybel_0(X0,X1,X8) | ~m1_connsp_2(X8,X0,X6)) | ~r2_hidden(X6,X2))) | ~m1_subset_1(X6,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : ((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2)) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((k10_yellow_6(X0,X1) = X2 | ? [X3] : (((? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2)) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | r2_hidden(X3,X2))) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (((r2_hidden(X3,X2) | ? [X4] : (~r1_waybel_0(X0,X1,X4) & m1_connsp_2(X4,X0,X3))) & (! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | k10_yellow_6(X0,X1) != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((k10_yellow_6(X0,X1) = X2 <=> ! [X3] : ((r2_hidden(X3,X2) <=> ! [X4] : (r1_waybel_0(X0,X1,X4) | ~m1_connsp_2(X4,X0,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (k10_yellow_6(X0,X1) = X2 <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) <=> ! [X4] : (m1_connsp_2(X4,X0,X3) => r1_waybel_0(X0,X1,X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).
% 0.21/0.50  fof(f979,plain,(
% 0.21/0.50    m1_connsp_2(sK4(sK0,sK3,sK1),sK0,sK1) | ~spl8_147),
% 0.21/0.50    inference(avatar_component_clause,[],[f977])).
% 0.21/0.50  fof(f977,plain,(
% 0.21/0.50    spl8_147 <=> m1_connsp_2(sK4(sK0,sK3,sK1),sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_147])])).
% 0.21/0.50  fof(f972,plain,(
% 0.21/0.50    ~r1_waybel_0(sK0,sK2,sK4(sK0,sK3,sK1)) | spl8_146),
% 0.21/0.50    inference(avatar_component_clause,[],[f970])).
% 0.21/0.50  fof(f970,plain,(
% 0.21/0.50    spl8_146 <=> r1_waybel_0(sK0,sK2,sK4(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_146])])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_68),
% 0.21/0.50    inference(avatar_component_clause,[],[f502])).
% 0.21/0.50  fof(f502,plain,(
% 0.21/0.50    spl8_68 <=> m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    r2_hidden(sK1,k10_yellow_6(sK0,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    (((~r2_hidden(sK1,k2_pre_topc(sK0,sK3)) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK1,k10_yellow_6(sK0,sK2)) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f31,f30,f29,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(sK0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X1,k10_yellow_6(sK0,X2)) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(sK0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(X1,k10_yellow_6(sK0,X2)) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (~r2_hidden(sK1,k2_pre_topc(sK0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK1,k10_yellow_6(sK0,X2)) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~r2_hidden(sK1,k2_pre_topc(sK0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(sK0),u1_waybel_0(sK0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK1,k10_yellow_6(sK0,X2)) & l1_waybel_0(X2,sK0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (? [X3] : (~r2_hidden(sK1,k2_pre_topc(sK0,X3)) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & r2_hidden(sK1,k10_yellow_6(sK0,sK2)) & l1_waybel_0(sK2,sK0) & v7_waybel_0(sK2) & v4_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ? [X3] : (~r2_hidden(sK1,k2_pre_topc(sK0,X3)) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r2_hidden(sK1,k2_pre_topc(sK0,sK3)) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2)) & l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~r2_hidden(X1,k2_pre_topc(X0,X3)) & k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r2_hidden(X1,k10_yellow_6(X0,X2))) & (l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((l1_waybel_0(X2,X0) & v7_waybel_0(X2) & v4_orders_2(X2) & ~v2_struct_0(X2)) => (r2_hidden(X1,k10_yellow_6(X0,X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (k2_relset_1(u1_struct_0(X2),u1_struct_0(X0),u1_waybel_0(X0,X2)) = X3 => r2_hidden(X1,k2_pre_topc(X0,X3))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_waybel_9)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    l1_waybel_0(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v7_waybel_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v4_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f980,plain,(
% 0.21/0.50    ~spl8_104 | spl8_147 | ~spl8_102 | ~spl8_78 | ~spl8_103),
% 0.21/0.50    inference(avatar_split_clause,[],[f974,f685,f556,f680,f977,f690])).
% 0.21/0.50  fof(f690,plain,(
% 0.21/0.50    spl8_104 <=> r2_hidden(sK1,sK4(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).
% 0.21/0.50  fof(f680,plain,(
% 0.21/0.50    spl8_102 <=> m1_subset_1(sK4(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 0.21/0.50  fof(f556,plain,(
% 0.21/0.50    spl8_78 <=> ! [X6] : (m1_connsp_2(X6,sK0,sK1) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X6,sK0) | ~r2_hidden(sK1,X6))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 0.21/0.50  fof(f685,plain,(
% 0.21/0.50    spl8_103 <=> v3_pre_topc(sK4(sK0,sK3,sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 0.21/0.50  fof(f974,plain,(
% 0.21/0.50    ~m1_subset_1(sK4(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK4(sK0,sK3,sK1),sK0,sK1) | ~r2_hidden(sK1,sK4(sK0,sK3,sK1)) | (~spl8_78 | ~spl8_103)),
% 0.21/0.50    inference(resolution,[],[f557,f687])).
% 0.21/0.50  fof(f687,plain,(
% 0.21/0.50    v3_pre_topc(sK4(sK0,sK3,sK1),sK0) | ~spl8_103),
% 0.21/0.50    inference(avatar_component_clause,[],[f685])).
% 0.21/0.50  fof(f557,plain,(
% 0.21/0.50    ( ! [X6] : (~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(X6,sK0,sK1) | ~r2_hidden(sK1,X6)) ) | ~spl8_78),
% 0.21/0.50    inference(avatar_component_clause,[],[f556])).
% 0.21/0.50  fof(f973,plain,(
% 0.21/0.50    ~spl8_146 | ~spl8_106 | ~spl8_69 | ~spl8_105),
% 0.21/0.50    inference(avatar_split_clause,[],[f968,f695,f507,f701,f970])).
% 0.21/0.50  fof(f701,plain,(
% 0.21/0.50    spl8_106 <=> r1_waybel_0(sK0,sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).
% 0.21/0.50  fof(f507,plain,(
% 0.21/0.50    spl8_69 <=> ! [X5,X6] : (~r1_xboole_0(X5,X6) | ~r1_waybel_0(sK0,sK2,X5) | ~r1_waybel_0(sK0,sK2,X6))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_69])])).
% 0.21/0.50  fof(f695,plain,(
% 0.21/0.50    spl8_105 <=> r1_xboole_0(sK3,sK4(sK0,sK3,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).
% 0.21/0.50  fof(f968,plain,(
% 0.21/0.50    ~r1_waybel_0(sK0,sK2,sK3) | ~r1_waybel_0(sK0,sK2,sK4(sK0,sK3,sK1)) | (~spl8_69 | ~spl8_105)),
% 0.21/0.50    inference(resolution,[],[f508,f697])).
% 0.21/0.50  fof(f697,plain,(
% 0.21/0.50    r1_xboole_0(sK3,sK4(sK0,sK3,sK1)) | ~spl8_105),
% 0.21/0.50    inference(avatar_component_clause,[],[f695])).
% 0.21/0.50  fof(f508,plain,(
% 0.21/0.50    ( ! [X6,X5] : (~r1_xboole_0(X5,X6) | ~r1_waybel_0(sK0,sK2,X5) | ~r1_waybel_0(sK0,sK2,X6)) ) | ~spl8_69),
% 0.21/0.50    inference(avatar_component_clause,[],[f507])).
% 0.21/0.50  fof(f753,plain,(
% 0.21/0.50    spl8_101),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f749])).
% 0.21/0.50  fof(f749,plain,(
% 0.21/0.50    $false | spl8_101),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f53,f678])).
% 0.21/0.50  fof(f678,plain,(
% 0.21/0.50    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl8_101),
% 0.21/0.50    inference(avatar_component_clause,[],[f676])).
% 0.21/0.50  fof(f676,plain,(
% 0.21/0.50    spl8_101 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f738,plain,(
% 0.21/0.50    spl8_83),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f734])).
% 0.21/0.50  fof(f734,plain,(
% 0.21/0.50    $false | spl8_83),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f47,f586])).
% 0.21/0.50  fof(f586,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl8_83),
% 0.21/0.50    inference(avatar_component_clause,[],[f584])).
% 0.21/0.50  fof(f584,plain,(
% 0.21/0.50    spl8_83 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 0.21/0.50  fof(f733,plain,(
% 0.21/0.50    spl8_82),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f730])).
% 0.21/0.50  fof(f730,plain,(
% 0.21/0.50    $false | spl8_82),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f51,f582])).
% 0.21/0.50  fof(f582,plain,(
% 0.21/0.50    ~l1_waybel_0(sK2,sK0) | spl8_82),
% 0.21/0.50    inference(avatar_component_clause,[],[f580])).
% 0.21/0.50  fof(f580,plain,(
% 0.21/0.50    spl8_82 <=> l1_waybel_0(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).
% 0.21/0.50  fof(f728,plain,(
% 0.21/0.50    ~spl8_62),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f725])).
% 0.21/0.50  fof(f725,plain,(
% 0.21/0.50    $false | ~spl8_62),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f48,f442])).
% 0.21/0.50  fof(f442,plain,(
% 0.21/0.50    v2_struct_0(sK2) | ~spl8_62),
% 0.21/0.50    inference(avatar_component_clause,[],[f440])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    spl8_62 <=> v2_struct_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).
% 0.21/0.50  fof(f723,plain,(
% 0.21/0.50    spl8_41),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f720])).
% 0.21/0.50  fof(f720,plain,(
% 0.21/0.50    $false | spl8_41),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f50,f349])).
% 0.21/0.50  fof(f349,plain,(
% 0.21/0.50    ~v7_waybel_0(sK2) | spl8_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f347])).
% 0.21/0.50  fof(f347,plain,(
% 0.21/0.50    spl8_41 <=> v7_waybel_0(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 0.21/0.50  fof(f719,plain,(
% 0.21/0.50    spl8_40),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f716])).
% 0.21/0.50  fof(f716,plain,(
% 0.21/0.50    $false | spl8_40),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f49,f345])).
% 0.21/0.50  fof(f345,plain,(
% 0.21/0.50    ~v4_orders_2(sK2) | spl8_40),
% 0.21/0.50    inference(avatar_component_clause,[],[f343])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    spl8_40 <=> v4_orders_2(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.21/0.50  fof(f715,plain,(
% 0.21/0.50    ~spl8_31),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f712])).
% 0.21/0.50  fof(f712,plain,(
% 0.21/0.50    $false | ~spl8_31),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f44,f240])).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    v2_struct_0(sK0) | ~spl8_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f238])).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    spl8_31 <=> v2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 0.21/0.50  fof(f707,plain,(
% 0.21/0.50    spl8_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f705])).
% 0.21/0.50  fof(f705,plain,(
% 0.21/0.50    $false | spl8_18),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f174,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ~l1_struct_0(sK0) | spl8_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f172])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    spl8_18 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.50  fof(f704,plain,(
% 0.21/0.50    spl8_31 | ~spl8_18 | spl8_62 | ~spl8_82 | spl8_106),
% 0.21/0.50    inference(avatar_split_clause,[],[f699,f701,f580,f440,f172,f238])).
% 0.21/0.50  fof(f699,plain,(
% 0.21/0.50    r1_waybel_0(sK0,sK2,sK3) | ~l1_waybel_0(sK2,sK0) | v2_struct_0(sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(superposition,[],[f68,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK0),u1_waybel_0(sK0,sK2)) = sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.21/0.50  fof(f698,plain,(
% 0.21/0.50    spl8_31 | ~spl8_1 | ~spl8_2 | ~spl8_101 | ~spl8_83 | spl8_105),
% 0.21/0.50    inference(avatar_split_clause,[],[f674,f695,f584,f676,f108,f104,f238])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    spl8_1 <=> v2_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    spl8_2 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f674,plain,(
% 0.21/0.50    r1_xboole_0(sK3,sK4(sK0,sK3,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f55,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r1_xboole_0(X1,sK4(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | (r1_xboole_0(X1,sK4(X0,X1,X2)) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK4(X0,X1,X2)) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (~r1_xboole_0(X1,X4) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(rectify,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(X2,k2_pre_topc(X0,X1)) | ? [X3] : (r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,k2_pre_topc(X0,X1)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : ((~r1_xboole_0(X1,X3) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k2_pre_topc(X0,X1)) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X3) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0)))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~r2_hidden(sK1,k2_pre_topc(sK0,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f693,plain,(
% 0.21/0.50    spl8_31 | ~spl8_1 | ~spl8_2 | ~spl8_101 | ~spl8_83 | spl8_104),
% 0.21/0.50    inference(avatar_split_clause,[],[f673,f690,f584,f676,f108,f104,f238])).
% 0.21/0.50  fof(f673,plain,(
% 0.21/0.50    r2_hidden(sK1,sK4(sK0,sK3,sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f55,f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | r2_hidden(X2,sK4(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f688,plain,(
% 0.21/0.50    spl8_31 | ~spl8_1 | ~spl8_2 | ~spl8_101 | ~spl8_83 | spl8_103),
% 0.21/0.50    inference(avatar_split_clause,[],[f672,f685,f584,f676,f108,f104,f238])).
% 0.21/0.50  fof(f672,plain,(
% 0.21/0.50    v3_pre_topc(sK4(sK0,sK3,sK1),sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f55,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | v3_pre_topc(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f683,plain,(
% 0.21/0.50    spl8_31 | ~spl8_1 | ~spl8_2 | ~spl8_101 | ~spl8_83 | spl8_102),
% 0.21/0.50    inference(avatar_split_clause,[],[f671,f680,f584,f676,f108,f104,f238])).
% 0.21/0.50  fof(f671,plain,(
% 0.21/0.50    m1_subset_1(sK4(sK0,sK3,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f55,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_pre_topc(X0,X1)) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f610,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f607])).
% 0.21/0.50  fof(f607,plain,(
% 0.21/0.50    $false | spl8_2),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f46,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f108])).
% 0.21/0.50  fof(f558,plain,(
% 0.21/0.50    spl8_31 | ~spl8_1 | ~spl8_2 | spl8_78),
% 0.21/0.50    inference(avatar_split_clause,[],[f531,f556,f108,f104,f238])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    ( ! [X6] : (m1_connsp_2(X6,sK0,sK1) | ~r2_hidden(sK1,X6) | ~v3_pre_topc(X6,sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f47,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.50  fof(f525,plain,(
% 0.21/0.50    spl8_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f522])).
% 0.21/0.50  fof(f522,plain,(
% 0.21/0.50    $false | spl8_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f45,f106])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f104])).
% 0.21/0.50  fof(f509,plain,(
% 0.21/0.50    spl8_31 | ~spl8_18 | spl8_62 | ~spl8_40 | ~spl8_41 | spl8_69),
% 0.21/0.50    inference(avatar_split_clause,[],[f476,f507,f347,f343,f440,f172,f238])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    ( ! [X6,X5] : (~r1_xboole_0(X5,X6) | ~r1_waybel_0(sK0,sK2,X6) | ~r1_waybel_0(sK0,sK2,X5) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.21/0.50    inference(resolution,[],[f51,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2,X3] : (~r1_xboole_0(X2,X3) | ~r1_waybel_0(X0,X1,X3) | ~r1_waybel_0(X0,X1,X2)) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2,X3] : ~(r1_xboole_0(X2,X3) & r1_waybel_0(X0,X1,X3) & r1_waybel_0(X0,X1,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_yellow_6)).
% 0.21/0.50  fof(f505,plain,(
% 0.21/0.50    spl8_31 | ~spl8_1 | ~spl8_2 | spl8_62 | ~spl8_40 | ~spl8_41 | spl8_68),
% 0.21/0.50    inference(avatar_split_clause,[],[f475,f502,f347,f343,f440,f108,f104,f238])).
% 0.21/0.50  fof(f475,plain,(
% 0.21/0.50    m1_subset_1(k10_yellow_6(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v7_waybel_0(sK2) | ~v4_orders_2(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f51,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (13338)------------------------------
% 0.21/0.50  % (13338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13338)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (13338)Memory used [KB]: 6908
% 0.21/0.50  % (13338)Time elapsed: 0.018 s
% 0.21/0.50  % (13338)------------------------------
% 0.21/0.50  % (13338)------------------------------
% 0.21/0.50  % (13325)Success in time 0.141 s
%------------------------------------------------------------------------------
