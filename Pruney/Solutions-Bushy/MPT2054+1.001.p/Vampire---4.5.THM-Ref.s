%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2054+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 541 expanded)
%              Number of leaves         :   54 ( 252 expanded)
%              Depth                    :   12
%              Number of atoms          : 1299 (3585 expanded)
%              Number of equality atoms :   14 (  36 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1057,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f111,f115,f119,f123,f127,f131,f135,f139,f143,f301,f356,f361,f366,f373,f377,f384,f410,f431,f457,f498,f780,f814,f819,f827,f834,f836,f922,f928,f935,f943,f951,f1036,f1046,f1052,f1056])).

fof(f1056,plain,
    ( spl7_10
    | ~ spl7_128
    | spl7_7
    | ~ spl7_4
    | spl7_149
    | ~ spl7_161 ),
    inference(avatar_split_clause,[],[f1054,f1050,f949,f117,f129,f829,f141])).

fof(f141,plain,
    ( spl7_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f829,plain,
    ( spl7_128
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_128])])).

fof(f129,plain,
    ( spl7_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f117,plain,
    ( spl7_4
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f949,plain,
    ( spl7_149
  <=> r1_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_149])])).

fof(f1050,plain,
    ( spl7_161
  <=> r2_hidden(sK5(sK0,sK1,sK2),k2_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_161])])).

fof(f1054,plain,
    ( r1_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_161 ),
    inference(resolution,[],[f1051,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_yellow19(X0,X1))
      | r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_yellow19(X0,X1))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ r1_waybel_0(X0,X1,X2) )
              & ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & r1_waybel_0(X0,X1,X2) )
                | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow19)).

fof(f1051,plain,
    ( r2_hidden(sK5(sK0,sK1,sK2),k2_yellow19(sK0,sK1))
    | ~ spl7_161 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f1052,plain,
    ( ~ spl7_51
    | spl7_161
    | ~ spl7_8
    | ~ spl7_129
    | ~ spl7_160 ),
    inference(avatar_split_clause,[],[f1047,f1044,f832,f133,f1050,f375])).

fof(f375,plain,
    ( spl7_51
  <=> m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f133,plain,
    ( spl7_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f832,plain,
    ( spl7_129
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_waybel_0(sK0,sK1,X3)
        | ~ r1_tarski(X3,X2)
        | r2_hidden(X2,k2_yellow19(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_129])])).

fof(f1044,plain,
    ( spl7_160
  <=> r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_160])])).

fof(f1047,plain,
    ( r2_hidden(sK5(sK0,sK1,sK2),k2_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_8
    | ~ spl7_129
    | ~ spl7_160 ),
    inference(resolution,[],[f1045,f839])).

fof(f839,plain,
    ( ! [X0] :
        ( ~ r1_waybel_0(sK0,sK1,k1_tops_1(sK0,X0))
        | r2_hidden(X0,k2_yellow19(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8
    | ~ spl7_129 ),
    inference(duplicate_literal_removal,[],[f838])).

fof(f838,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_yellow19(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_waybel_0(sK0,sK1,k1_tops_1(sK0,X0)) )
    | ~ spl7_8
    | ~ spl7_129 ),
    inference(resolution,[],[f837,f134])).

fof(f134,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f837,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_yellow19(sK0,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ r1_waybel_0(sK0,sK1,k1_tops_1(X0,X1)) )
    | ~ spl7_129 ),
    inference(resolution,[],[f833,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f833,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(X3,X2)
        | ~ r1_waybel_0(sK0,sK1,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,k2_yellow19(sK0,sK1)) )
    | ~ spl7_129 ),
    inference(avatar_component_clause,[],[f832])).

fof(f1045,plain,
    ( r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl7_160 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1046,plain,
    ( spl7_10
    | ~ spl7_128
    | spl7_7
    | ~ spl7_4
    | spl7_160
    | ~ spl7_158 ),
    inference(avatar_split_clause,[],[f1042,f1034,f1044,f117,f129,f829,f141])).

fof(f1034,plain,
    ( spl7_158
  <=> r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),k2_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_158])])).

fof(f1042,plain,
    ( r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_158 ),
    inference(resolution,[],[f1035,f74])).

fof(f1035,plain,
    ( r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),k2_yellow19(sK0,sK1))
    | ~ spl7_158 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f1036,plain,
    ( spl7_158
    | ~ spl7_2
    | ~ spl7_50
    | ~ spl7_62 ),
    inference(avatar_split_clause,[],[f1031,f455,f371,f106,f1034])).

fof(f106,plain,
    ( spl7_2
  <=> r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f371,plain,
    ( spl7_50
  <=> r2_hidden(sK2,k1_tops_1(sK0,sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f455,plain,
    ( spl7_62
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
        | r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),X1)
        | ~ r2_waybel_7(sK0,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f1031,plain,
    ( r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),k2_yellow19(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_50
    | ~ spl7_62 ),
    inference(resolution,[],[f968,f110])).

fof(f110,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f968,plain,
    ( ! [X0] :
        ( ~ r2_waybel_7(sK0,X0,sK2)
        | r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),X0) )
    | ~ spl7_50
    | ~ spl7_62 ),
    inference(resolution,[],[f372,f456])).

fof(f456,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
        | r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),X1)
        | ~ r2_waybel_7(sK0,X1,X0) )
    | ~ spl7_62 ),
    inference(avatar_component_clause,[],[f455])).

fof(f372,plain,
    ( r2_hidden(sK2,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f371])).

fof(f951,plain,
    ( ~ spl7_149
    | spl7_1
    | ~ spl7_3
    | ~ spl7_120 ),
    inference(avatar_split_clause,[],[f781,f778,f113,f103,f949])).

fof(f103,plain,
    ( spl7_1
  <=> r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f113,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f778,plain,
    ( spl7_120
  <=> ! [X0] :
        ( r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,sK1,sK5(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_120])])).

fof(f781,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ r1_waybel_0(sK0,sK1,sK5(sK0,sK1,sK2))
    | ~ spl7_3
    | ~ spl7_120 ),
    inference(resolution,[],[f779,f114])).

fof(f114,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f113])).

fof(f779,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ r1_waybel_0(sK0,sK1,sK5(sK0,sK1,X0)) )
    | ~ spl7_120 ),
    inference(avatar_component_clause,[],[f778])).

fof(f943,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | spl7_2
    | ~ spl7_146 ),
    inference(avatar_split_clause,[],[f940,f933,f106,f133,f137])).

fof(f137,plain,
    ( spl7_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f933,plain,
    ( spl7_146
  <=> r2_hidden(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k2_yellow19(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_146])])).

fof(f940,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl7_146 ),
    inference(resolution,[],[f934,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(X2,sK6(X0,X1,X2))
              & v3_pre_topc(sK6(X0,X1,X2),X0)
              & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(X2,sK6(X0,X1,X2))
        & v3_pre_topc(sK6(X0,X1,X2),X0)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f934,plain,
    ( r2_hidden(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k2_yellow19(sK0,sK1))
    | ~ spl7_146 ),
    inference(avatar_component_clause,[],[f933])).

fof(f935,plain,
    ( spl7_146
    | ~ spl7_52
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_127
    | ~ spl7_145 ),
    inference(avatar_split_clause,[],[f929,f926,f825,f113,f103,f382,f933])).

fof(f382,plain,
    ( spl7_52
  <=> m1_subset_1(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f825,plain,
    ( spl7_127
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
        | ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_127])])).

fof(f926,plain,
    ( spl7_145
  <=> m1_connsp_2(sK6(sK0,k2_yellow19(sK0,sK1),sK2),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_145])])).

fof(f929,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k2_yellow19(sK0,sK1))
    | ~ spl7_127
    | ~ spl7_145 ),
    inference(resolution,[],[f927,f826])).

fof(f826,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_yellow19(sK0,sK1)) )
    | ~ spl7_127 ),
    inference(avatar_component_clause,[],[f825])).

fof(f927,plain,
    ( m1_connsp_2(sK6(sK0,k2_yellow19(sK0,sK1),sK2),sK0,sK2)
    | ~ spl7_145 ),
    inference(avatar_component_clause,[],[f926])).

fof(f928,plain,
    ( spl7_145
    | spl7_2
    | ~ spl7_52
    | ~ spl7_144 ),
    inference(avatar_split_clause,[],[f923,f920,f382,f106,f926])).

fof(f920,plain,
    ( spl7_144
  <=> ! [X0] :
        ( m1_connsp_2(sK6(sK0,X0,sK2),sK0,sK2)
        | r2_waybel_7(sK0,X0,sK2)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_144])])).

fof(f923,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | m1_connsp_2(sK6(sK0,k2_yellow19(sK0,sK1),sK2),sK0,sK2)
    | ~ spl7_52
    | ~ spl7_144 ),
    inference(resolution,[],[f921,f383])).

fof(f383,plain,
    ( m1_subset_1(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f382])).

fof(f921,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_waybel_7(sK0,X0,sK2)
        | m1_connsp_2(sK6(sK0,X0,sK2),sK0,sK2) )
    | ~ spl7_144 ),
    inference(avatar_component_clause,[],[f920])).

fof(f922,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | spl7_144
    | ~ spl7_3
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f918,f299,f113,f920,f133,f137])).

fof(f299,plain,
    ( spl7_37
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v3_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f918,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK6(sK0,X0,sK2),sK0,sK2)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_waybel_7(sK0,X0,sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_3
    | ~ spl7_37 ),
    inference(duplicate_literal_removal,[],[f917])).

fof(f917,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK6(sK0,X0,sK2),sK0,sK2)
        | ~ m1_subset_1(sK6(sK0,X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_waybel_7(sK0,X0,sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | r2_waybel_7(sK0,X0,sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_3
    | ~ spl7_37 ),
    inference(resolution,[],[f303,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK6(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(sK6(X0,X1,sK2),sK0)
        | m1_connsp_2(sK6(X0,X1,sK2),sK0,sK2)
        | ~ m1_subset_1(sK6(X0,X1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_waybel_7(X0,X1,sK2)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl7_3
    | ~ spl7_37 ),
    inference(resolution,[],[f302,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK6(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f302,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X0,sK0,sK2)
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl7_3
    | ~ spl7_37 ),
    inference(resolution,[],[f300,f114])).

fof(f300,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,X1)
        | ~ v3_pre_topc(X1,sK0) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f299])).

fof(f836,plain,
    ( ~ spl7_8
    | spl7_128 ),
    inference(avatar_split_clause,[],[f835,f829,f133])).

fof(f835,plain,
    ( ~ l1_pre_topc(sK0)
    | spl7_128 ),
    inference(resolution,[],[f830,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f830,plain,
    ( ~ l1_struct_0(sK0)
    | spl7_128 ),
    inference(avatar_component_clause,[],[f829])).

fof(f834,plain,
    ( spl7_10
    | ~ spl7_128
    | spl7_7
    | ~ spl7_4
    | spl7_129
    | ~ spl7_126 ),
    inference(avatar_split_clause,[],[f821,f817,f832,f117,f129,f829,f141])).

fof(f817,plain,
    ( spl7_126
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_waybel_0(sK0,sK1,X0)
        | r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_126])])).

fof(f821,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,k2_yellow19(sK0,sK1))
        | ~ r1_waybel_0(sK0,sK1,X3)
        | ~ r1_tarski(X3,X2)
        | ~ l1_waybel_0(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_struct_0(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_126 ),
    inference(resolution,[],[f818,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_0(X0,X1,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ r1_tarski(X2,X3)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

fof(f818,plain,
    ( ! [X0] :
        ( ~ r1_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_yellow19(sK0,sK1)) )
    | ~ spl7_126 ),
    inference(avatar_component_clause,[],[f817])).

fof(f827,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | spl7_7
    | ~ spl7_6
    | ~ spl7_5
    | ~ spl7_4
    | spl7_127
    | ~ spl7_126 ),
    inference(avatar_split_clause,[],[f820,f817,f825,f117,f121,f125,f129,f133,f137,f141])).

fof(f125,plain,
    ( spl7_6
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f121,plain,
    ( spl7_5
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f820,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_yellow19(sK0,sK1))
        | ~ m1_connsp_2(X0,sK0,X1)
        | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_waybel_0(sK1,sK0)
        | ~ v7_waybel_0(sK1)
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_126 ),
    inference(resolution,[],[f818,f144])).

fof(f144,plain,(
    ! [X6,X0,X8,X1] :
      ( r1_waybel_0(X0,X1,X8)
      | ~ m1_connsp_2(X8,X0,X6)
      | ~ r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f101,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_yellow_6)).

fof(f101,plain,(
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
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k10_yellow_6(X0,X1) = X2
                  | ( ( ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
                        & m1_connsp_2(sK4(X0,X1,X2),X0,sK3(X0,X1,X2)) )
                      | ~ r2_hidden(sK3(X0,X1,X2),X2) )
                    & ( ! [X5] :
                          ( r1_waybel_0(X0,X1,X5)
                          | ~ m1_connsp_2(X5,X0,sK3(X0,X1,X2)) )
                      | r2_hidden(sK3(X0,X1,X2),X2) )
                    & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
                            & m1_connsp_2(sK5(X0,X1,X6),X0,X6) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f53,f56,f55,f54])).

fof(f54,plain,(
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
              & m1_connsp_2(X4,X0,sK3(X0,X1,X2)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ! [X5] :
              ( r1_waybel_0(X0,X1,X5)
              | ~ m1_connsp_2(X5,X0,sK3(X0,X1,X2)) )
          | r2_hidden(sK3(X0,X1,X2),X2) )
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_waybel_0(X0,X1,X4)
          & m1_connsp_2(X4,X0,sK3(X0,X1,X2)) )
     => ( ~ r1_waybel_0(X0,X1,sK4(X0,X1,X2))
        & m1_connsp_2(sK4(X0,X1,X2),X0,sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X6,X1,X0] :
      ( ? [X7] :
          ( ~ r1_waybel_0(X0,X1,X7)
          & m1_connsp_2(X7,X0,X6) )
     => ( ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
        & m1_connsp_2(sK5(X0,X1,X6),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_yellow_6)).

fof(f819,plain,
    ( spl7_7
    | spl7_126
    | ~ spl7_4
    | ~ spl7_125 ),
    inference(avatar_split_clause,[],[f815,f812,f117,f817,f129])).

fof(f812,plain,
    ( spl7_125
  <=> ! [X1,X0] :
        ( ~ r1_waybel_0(sK0,X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_125])])).

fof(f815,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X0,k2_yellow19(sK0,sK1))
        | v2_struct_0(sK1)
        | ~ r1_waybel_0(sK0,sK1,X0) )
    | ~ spl7_4
    | ~ spl7_125 ),
    inference(resolution,[],[f813,f118])).

fof(f118,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f813,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,k2_yellow19(sK0,X0))
        | v2_struct_0(X0)
        | ~ r1_waybel_0(sK0,X0,X1) )
    | ~ spl7_125 ),
    inference(avatar_component_clause,[],[f812])).

fof(f814,plain,
    ( spl7_10
    | spl7_125
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f810,f133,f812,f141])).

fof(f810,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(sK0,X0,X1)
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | r2_hidden(X1,k2_yellow19(sK0,X0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_8 ),
    inference(resolution,[],[f194,f134])).

fof(f194,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r1_waybel_0(X1,X2,X0)
      | ~ l1_waybel_0(X2,X1)
      | v2_struct_0(X2)
      | r2_hidden(X0,k2_yellow19(X1,X2))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f76,f72])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(X2,k2_yellow19(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f780,plain,
    ( spl7_120
    | ~ spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_4
    | ~ spl7_70 ),
    inference(avatar_split_clause,[],[f776,f496,f117,f141,f137,f133,f778])).

fof(f496,plain,
    ( spl7_70
  <=> ! [X1,X0] :
        ( ~ r1_waybel_0(X0,sK1,sK5(X0,sK1,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f776,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ r1_waybel_0(sK0,sK1,sK5(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_70 ),
    inference(resolution,[],[f497,f118])).

fof(f497,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ r1_waybel_0(X0,sK1,sK5(X0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl7_70 ),
    inference(avatar_component_clause,[],[f496])).

fof(f498,plain,
    ( spl7_7
    | ~ spl7_6
    | spl7_70
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f494,f121,f496,f125,f129])).

fof(f494,plain,
    ( ! [X0,X1] :
        ( ~ r1_waybel_0(X0,sK1,sK5(X0,sK1,X1))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f146,f122])).

fof(f122,plain,
    ( v7_waybel_0(sK1)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f146,plain,(
    ! [X6,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f99,f94])).

fof(f99,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | ~ r1_waybel_0(X0,X1,sK5(X0,X1,X6))
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
    inference(cnf_transformation,[],[f57])).

fof(f457,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | ~ spl7_53
    | spl7_62
    | ~ spl7_55 ),
    inference(avatar_split_clause,[],[f451,f396,f455,f390,f133,f137])).

fof(f390,plain,
    ( spl7_53
  <=> v3_pre_topc(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f396,plain,
    ( spl7_55
  <=> m1_subset_1(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f451,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
        | ~ v3_pre_topc(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),sK0)
        | r2_hidden(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),X1)
        | ~ r2_waybel_7(sK0,X1,X0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl7_55 ),
    inference(resolution,[],[f409,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | r2_hidden(X4,X1)
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f409,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_55 ),
    inference(avatar_component_clause,[],[f396])).

fof(f431,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | ~ spl7_51
    | spl7_53 ),
    inference(avatar_split_clause,[],[f416,f390,f375,f133,f137])).

fof(f416,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_53 ),
    inference(resolution,[],[f391,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f391,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),sK0)
    | spl7_53 ),
    inference(avatar_component_clause,[],[f390])).

fof(f410,plain,
    ( ~ spl7_8
    | spl7_55
    | ~ spl7_51 ),
    inference(avatar_split_clause,[],[f400,f375,f396,f133])).

fof(f400,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK5(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl7_51 ),
    inference(resolution,[],[f376,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f376,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f375])).

fof(f384,plain,
    ( ~ spl7_9
    | ~ spl7_8
    | spl7_52
    | spl7_2 ),
    inference(avatar_split_clause,[],[f380,f106,f382,f133,f137])).

fof(f380,plain,
    ( m1_subset_1(sK6(sK0,k2_yellow19(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl7_2 ),
    inference(resolution,[],[f107,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f107,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f377,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_3
    | spl7_51
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f368,f364,f375,f113,f133,f137,f141])).

fof(f364,plain,
    ( spl7_49
  <=> m1_connsp_2(sK5(sK0,sK1,sK2),sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f368,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_49 ),
    inference(resolution,[],[f365,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f365,plain,
    ( m1_connsp_2(sK5(sK0,sK1,sK2),sK0,sK2)
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f364])).

fof(f373,plain,
    ( spl7_10
    | ~ spl7_9
    | ~ spl7_8
    | ~ spl7_3
    | spl7_50
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f367,f364,f371,f113,f133,f137,f141])).

fof(f367,plain,
    ( r2_hidden(sK2,k1_tops_1(sK0,sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_49 ),
    inference(resolution,[],[f365,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f79,f95])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

% (16551)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f366,plain,
    ( spl7_49
    | spl7_1
    | ~ spl7_3
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f362,f359,f113,f103,f364])).

fof(f359,plain,
    ( spl7_48
  <=> ! [X0] :
        ( r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK5(sK0,sK1,X0),sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f362,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | m1_connsp_2(sK5(sK0,sK1,sK2),sK0,sK2)
    | ~ spl7_3
    | ~ spl7_48 ),
    inference(resolution,[],[f360,f114])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | m1_connsp_2(sK5(sK0,sK1,X0),sK0,X0) )
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( spl7_48
    | ~ spl7_8
    | ~ spl7_9
    | spl7_10
    | ~ spl7_4
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f357,f354,f117,f141,f137,f133,f359])).

fof(f354,plain,
    ( spl7_47
  <=> ! [X1,X0] :
        ( m1_connsp_2(sK5(X0,sK1,X1),X0,X1)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ l1_waybel_0(sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f357,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(X0,k10_yellow_6(sK0,sK1))
        | m1_connsp_2(sK5(sK0,sK1,X0),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_4
    | ~ spl7_47 ),
    inference(resolution,[],[f355,f118])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(sK1,X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | m1_connsp_2(sK5(X0,sK1,X1),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0)) )
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f354])).

fof(f356,plain,
    ( spl7_7
    | ~ spl7_6
    | spl7_47
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f352,f121,f354,f125,f129])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( m1_connsp_2(sK5(X0,sK1,X1),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_waybel_0(sK1,X0)
        | r2_hidden(X1,k10_yellow_6(X0,sK1))
        | ~ v4_orders_2(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl7_5 ),
    inference(resolution,[],[f145,f122])).

fof(f145,plain,(
    ! [X6,X0,X1] :
      ( ~ v7_waybel_0(X1)
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(X6,k10_yellow_6(X0,X1))
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f100,f94])).

fof(f100,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(X6,k10_yellow_6(X0,X1))
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,X2)
      | m1_connsp_2(sK5(X0,X1,X6),X0,X6)
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
    inference(cnf_transformation,[],[f57])).

fof(f301,plain,
    ( spl7_10
    | ~ spl7_9
    | spl7_37
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f297,f133,f299,f137,f141])).

fof(f297,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(X1,sK0,X0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_8 ),
    inference(resolution,[],[f81,f134])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_connsp_2(X1,X0,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f143,plain,(
    ~ spl7_10 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
      | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) )
    & ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & v4_orders_2(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                  | r2_hidden(X2,k10_yellow_6(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(sK0,X1)) )
              & ( r2_waybel_7(sK0,k2_yellow19(sK0,X1),X2)
                | r2_hidden(X2,k10_yellow_6(sK0,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,X1),X2)
              | ~ r2_hidden(X2,k10_yellow_6(sK0,X1)) )
            & ( r2_waybel_7(sK0,k2_yellow19(sK0,X1),X2)
              | r2_hidden(X2,k10_yellow_6(sK0,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & l1_waybel_0(X1,sK0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X2)
            | ~ r2_hidden(X2,k10_yellow_6(sK0,sK1)) )
          & ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X2)
            | r2_hidden(X2,k10_yellow_6(sK0,sK1)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & l1_waybel_0(sK1,sK0)
      & v7_waybel_0(sK1)
      & v4_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X2] :
        ( ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X2)
          | ~ r2_hidden(X2,k10_yellow_6(sK0,sK1)) )
        & ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X2)
          | r2_hidden(X2,k10_yellow_6(sK0,sK1)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
        | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) )
      & ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
        | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & ( r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
                | r2_hidden(X2,k10_yellow_6(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <~> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <~> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
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
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,X1))
                <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

fof(f139,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f63,f137])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f135,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f64,f133])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f131,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f65,f129])).

fof(f65,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f127,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f66,f125])).

fof(f66,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f67,f121])).

fof(f67,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f119,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f68,f117])).

fof(f68,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f115,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f69,f113])).

fof(f69,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f70,f106,f103])).

fof(f70,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f71,f106,f103])).

fof(f71,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f47])).

%------------------------------------------------------------------------------
