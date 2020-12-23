%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t49_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 23.07s
% Output     : Refutation 23.10s
% Verified   : 
% Statistics : Number of formulae       :  616 (4658 expanded)
%              Number of leaves         :  133 (1403 expanded)
%              Depth                    :   22
%              Number of atoms          : 2990 (15870 expanded)
%              Number of equality atoms :    7 ( 329 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :   13 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66886,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f153,f157,f164,f171,f178,f185,f192,f199,f206,f213,f220,f227,f234,f241,f251,f258,f265,f275,f292,f305,f306,f319,f331,f332,f340,f352,f401,f410,f412,f441,f531,f1149,f1182,f1185,f1186,f1191,f1258,f1266,f1274,f1285,f1332,f1629,f1637,f1730,f2890,f4060,f4445,f8036,f9434,f11035,f11040,f13833,f13841,f13849,f13859,f13868,f14242,f17416,f17882,f18116,f18136,f20784,f25052,f26047,f26472,f28509,f28554,f28562,f32086,f32630,f37922,f45841,f46674,f47294,f51861,f52387,f52396,f54907,f59945,f64104,f65398,f66879,f66882,f66883,f66884,f66885])).

fof(f66885,plain,
    ( spl13_0
    | spl13_18
    | ~ spl13_17
    | ~ spl13_15
    | spl13_24
    | ~ spl13_23
    | ~ spl13_21
    | ~ spl13_13
    | ~ spl13_11
    | ~ spl13_9
    | ~ spl13_77
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f66881,f155,f1253,f159,f166,f173,f201,f208,f215,f180,f187,f194,f135])).

fof(f135,plain,
    ( spl13_0
  <=> v5_pre_topc(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f194,plain,
    ( spl13_18
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_18])])).

fof(f187,plain,
    ( spl13_17
  <=> ~ v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f180,plain,
    ( spl13_15
  <=> ~ l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_15])])).

fof(f215,plain,
    ( spl13_24
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_24])])).

fof(f208,plain,
    ( spl13_23
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_23])])).

fof(f201,plain,
    ( spl13_21
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_21])])).

fof(f173,plain,
    ( spl13_13
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_13])])).

fof(f166,plain,
    ( spl13_11
  <=> ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_11])])).

fof(f159,plain,
    ( spl13_9
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_9])])).

fof(f1253,plain,
    ( spl13_77
  <=> ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_77])])).

fof(f155,plain,
    ( spl13_6
  <=> ! [X4] :
        ( r1_tmap_1(sK1,sK0,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f66881,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ spl13_6 ),
    inference(resolution,[],[f156,f17988])).

fof(f17988,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(global_subsumption,[],[f110,f109,f17987])).

fof(f17987,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) ) ),
    inference(duplicate_literal_removal,[],[f17984])).

fof(f17984,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | ~ r1_tmap_1(X0,X1,X2,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(resolution,[],[f5109,f3418])).

fof(f3418,plain,(
    ! [X6,X4,X5] :
      ( m1_connsp_2(sK8(X4,X5,X6,sK4(X4,X5,X6),sK5(X4,X5,X6)),X4,sK4(X4,X5,X6))
      | ~ r1_tmap_1(X4,X5,X6,sK4(X4,X5,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v5_pre_topc(X6,X4,X5) ) ),
    inference(global_subsumption,[],[f109,f3416])).

fof(f3416,plain,(
    ! [X6,X4,X5] :
      ( m1_connsp_2(sK8(X4,X5,X6,sK4(X4,X5,X6),sK5(X4,X5,X6)),X4,sK4(X4,X5,X6))
      | ~ r1_tmap_1(X4,X5,X6,sK4(X4,X5,X6))
      | ~ m1_subset_1(sK4(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v5_pre_topc(X6,X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f3411])).

fof(f3411,plain,(
    ! [X6,X4,X5] :
      ( m1_connsp_2(sK8(X4,X5,X6,sK4(X4,X5,X6),sK5(X4,X5,X6)),X4,sK4(X4,X5,X6))
      | ~ r1_tmap_1(X4,X5,X6,sK4(X4,X5,X6))
      | ~ m1_subset_1(sK4(X4,X5,X6),u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | v5_pre_topc(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f112,f110])).

fof(f112,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | m1_connsp_2(sK8(X0,X1,X2,X3,X6),X0,X3)
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ( ! [X5] :
                            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
                            | ~ m1_connsp_2(X5,X0,X3) )
                        & m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
                            & m1_connsp_2(sK8(X0,X1,X2,X3,X6),X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f78,f80,f79])).

fof(f79,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,X3) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
            | ~ m1_connsp_2(X5,X0,X3) )
        & m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X6,X3,X2,X1,X0] :
      ( ? [X7] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
          & m1_connsp_2(X7,X0,X3) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
        & m1_connsp_2(sK8(X0,X1,X2,X3,X6),X0,X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X6] :
                          ( ? [X7] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X7),X6)
                              & m1_connsp_2(X7,X0,X3) )
                          | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r1_tmap_1(X0,X1,X2,X3)
                      | ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                    & ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ r1_tmap_1(X0,X1,X2,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',d2_tmap_1)).

fof(f5109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(sK8(X0,X1,X2,X3,sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f5051])).

fof(f5051,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(sK8(X0,X1,X2,X3,sK5(X0,X1,X2)),X0,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f113,f111])).

fof(f111,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ! [X5] :
                        ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
                        | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
                    & m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X6,X7)),X7)
                            & m1_connsp_2(sK6(X0,X1,X2,X6,X7),X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f72,f75,f74,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                  | ~ m1_connsp_2(X5,X0,X3) )
              & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ! [X5] :
                ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2)) )
            & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
              | ~ m1_connsp_2(X5,X0,X3) )
          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
     => ( ! [X5] :
            ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
            | ~ m1_connsp_2(X5,X0,X3) )
        & m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X7,X6,X2,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
          & m1_connsp_2(X8,X0,X6) )
     => ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X6,X7)),X7)
        & m1_connsp_2(sK6(X0,X1,X2,X6,X7),X0,X6) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ! [X7] :
                          ( ? [X8] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X8),X7)
                              & m1_connsp_2(X8,X0,X6) )
                          | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6)) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ? [X4] :
                          ( ! [X5] :
                              ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              | ~ m1_connsp_2(X5,X0,X3) )
                          & m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ! [X4] :
                          ( ? [X5] :
                              ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                              & m1_connsp_2(X5,X0,X3) )
                          | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',d3_borsuk_1)).

fof(f113,plain,(
    ! [X6,X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X6)),X6)
      | ~ m1_connsp_2(X6,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f156,plain,
    ( ! [X4] :
        ( r1_tmap_1(sK1,sK0,sK2,X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f155])).

fof(f66884,plain,
    ( spl13_4
    | ~ spl13_78 ),
    inference(avatar_split_clause,[],[f1276,f1264,f151])).

fof(f151,plain,
    ( spl13_4
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f1264,plain,
    ( spl13_78
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_78])])).

fof(f1276,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_78 ),
    inference(resolution,[],[f1265,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t1_subset)).

fof(f1265,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl13_78 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f66883,plain,
    ( spl13_76
    | spl13_18
    | ~ spl13_17
    | ~ spl13_15
    | spl13_24
    | ~ spl13_23
    | ~ spl13_21
    | ~ spl13_13
    | ~ spl13_11
    | spl13_0
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f5861,f273,f135,f166,f173,f201,f208,f215,f180,f187,f194,f1256])).

fof(f1256,plain,
    ( spl13_76
  <=> m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_76])])).

fof(f273,plain,
    ( spl13_38
  <=> r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_38])])).

fof(f5861,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_38 ),
    inference(resolution,[],[f1232,f274])).

fof(f274,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl13_38 ),
    inference(avatar_component_clause,[],[f273])).

fof(f1232,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f109,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t3_subset)).

fof(f66882,plain,
    ( ~ spl13_5
    | spl13_3
    | ~ spl13_6 ),
    inference(avatar_split_clause,[],[f66880,f155,f144,f148])).

fof(f148,plain,
    ( spl13_5
  <=> ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_5])])).

fof(f144,plain,
    ( spl13_3
  <=> ~ r1_tmap_1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_3])])).

fof(f66880,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_3
    | ~ spl13_6 ),
    inference(resolution,[],[f156,f145])).

fof(f145,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl13_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f66879,plain,
    ( spl13_6
    | spl13_18
    | ~ spl13_17
    | ~ spl13_15
    | spl13_24
    | ~ spl13_23
    | ~ spl13_21
    | ~ spl13_13
    | ~ spl13_11
    | ~ spl13_1
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f66824,f162,f138,f166,f173,f201,f208,f215,f180,f187,f194,f155])).

fof(f138,plain,
    ( spl13_1
  <=> ~ v5_pre_topc(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f162,plain,
    ( spl13_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_8])])).

fof(f66824,plain,
    ( ! [X556] :
        ( ~ v5_pre_topc(sK2,sK1,sK0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | r1_tmap_1(sK1,sK0,sK2,X556)
        | ~ m1_subset_1(X556,u1_struct_0(sK1)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f33036,f163])).

fof(f163,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f33036,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v5_pre_topc(X0,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f33033])).

fof(f33033,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X2,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v5_pre_topc(X0,X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X2,X0,X3) ) ),
    inference(resolution,[],[f18702,f2948])).

fof(f2948,plain,(
    ! [X10,X8,X7,X9] :
      ( m1_connsp_2(sK6(X7,X8,X9,X10,sK7(X7,X8,X9,X10)),X7,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X7))
      | ~ v5_pre_topc(X9,X7,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | r1_tmap_1(X7,X8,X9,X10) ) ),
    inference(duplicate_literal_removal,[],[f2945])).

fof(f2945,plain,(
    ! [X10,X8,X7,X9] :
      ( m1_connsp_2(sK6(X7,X8,X9,X10,sK7(X7,X8,X9,X10)),X7,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X7))
      | ~ v5_pre_topc(X9,X7,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7)
      | r1_tmap_1(X7,X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X7))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X7),u1_struct_0(X8))))
      | ~ v1_funct_2(X9,u1_struct_0(X7),u1_struct_0(X8))
      | ~ v1_funct_1(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(X7)
      | ~ v2_pre_topc(X7)
      | v2_struct_0(X7) ) ),
    inference(resolution,[],[f107,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f107,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | m1_connsp_2(sK6(X0,X1,X2,X6,X7),X0,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f18702,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(sK6(X1,X3,X2,X0,sK7(X1,X3,X2,X0)),X1,X0)
      | ~ v5_pre_topc(X2,X1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X3,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f18699])).

fof(f18699,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | r1_tmap_1(X1,X3,X2,X0)
      | ~ m1_connsp_2(sK6(X1,X3,X2,X0,sK7(X1,X3,X2,X0)),X1,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | r1_tmap_1(X1,X3,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f4117,f114])).

fof(f4117,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ m1_connsp_2(sK7(X4,X5,X6,X7),X5,k3_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X4))
      | ~ v5_pre_topc(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r1_tmap_1(X4,X5,X6,X7)
      | ~ m1_connsp_2(sK6(X4,X5,X6,X8,sK7(X4,X5,X6,X7)),X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f4065])).

fof(f4065,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ m1_connsp_2(sK7(X4,X5,X6,X7),X5,k3_funct_2(u1_struct_0(X4),u1_struct_0(X5),X6,X8))
      | ~ m1_subset_1(X8,u1_struct_0(X4))
      | ~ v5_pre_topc(X6,X4,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4)
      | r1_tmap_1(X4,X5,X6,X7)
      | ~ m1_connsp_2(sK6(X4,X5,X6,X8,sK7(X4,X5,X6,X7)),X4,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X5))))
      | ~ v1_funct_2(X6,u1_struct_0(X4),u1_struct_0(X5))
      | ~ v1_funct_1(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f108,f115])).

fof(f115,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_connsp_2(X5,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f108,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X6,X7)),X7)
      | ~ m1_connsp_2(X7,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f65398,plain,
    ( spl13_56
    | spl13_164
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f65394,f28507,f65396,f393])).

fof(f393,plain,
    ( spl13_56
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_56])])).

fof(f65396,plain,
    ( spl13_164
  <=> ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0)))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0))))))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0))))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_164])])).

fof(f28507,plain,
    ( spl13_134
  <=> ! [X448] :
        ( ~ m1_subset_1(X448,u1_struct_0(sK1))
        | r1_tarski(sK7(sK1,sK0,sK2,X448),u1_struct_0(sK0))
        | ~ m1_subset_1(k1_funct_1(sK2,X448),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X448) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_134])])).

fof(f65394,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0))))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0)))))),u1_struct_0(sK0)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28517,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t2_subset)).

fof(f28517,plain,
    ( ! [X13] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X13)))))),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X13),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X13))))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X13))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X13)))))) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28510,f629])).

fof(f629,plain,(
    ! [X28] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X28))))),X28)
      | v1_xboole_0(sK9(k1_zfmisc_1(X28)))
      | v1_xboole_0(X28)
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X28))))) ) ),
    inference(resolution,[],[f370,f119])).

fof(f370,plain,(
    ! [X3] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X3))))),X3)
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X3)))))
      | v1_xboole_0(sK9(k1_zfmisc_1(X3))) ) ),
    inference(resolution,[],[f362,f323])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK9(k1_zfmisc_1(X1)))
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f126,f116])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK9(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f22,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK9(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',existence_m1_subset_1)).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t4_subset)).

fof(f362,plain,(
    ! [X5] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(X5))),X5)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK9(k1_zfmisc_1(X5))) ) ),
    inference(resolution,[],[f326,f119])).

fof(f326,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK9(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f323,f277])).

fof(f277,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f116])).

fof(f28510,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,sK7(sK1,sK0,sK2,X0))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28508,f325])).

fof(f325,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X4)
      | ~ r2_hidden(X3,X5)
      | m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f126,f123])).

fof(f28508,plain,
    ( ! [X448] :
        ( r1_tarski(sK7(sK1,sK0,sK2,X448),u1_struct_0(sK0))
        | ~ m1_subset_1(X448,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X448),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X448) )
    | ~ spl13_134 ),
    inference(avatar_component_clause,[],[f28507])).

fof(f64104,plain,
    ( spl13_56
    | spl13_162
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f64100,f162,f64102,f393])).

fof(f64102,plain,
    ( spl13_162
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))))))),X4),X5),X6))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))))))),X4),X5),X6)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_162])])).

fof(f64100,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))))))),X4),X5),X6))
        | v1_xboole_0(k9_relat_1(sK2,X3))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))))))),X4),X5),X6)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f64001,f119])).

fof(f64001,plain,
    ( ! [X629,X625,X627,X623,X628,X624,X626] :
        ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X624,k2_zfmisc_1(X625,k2_zfmisc_1(X626,sK9(k1_zfmisc_1(k9_relat_1(sK2,X623)))))))),X627),X628),X629)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X624,k2_zfmisc_1(X625,k2_zfmisc_1(X626,sK9(k1_zfmisc_1(k9_relat_1(sK2,X623)))))))),X627),X628),X629))
        | v1_xboole_0(k9_relat_1(sK2,X623)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f38702,f390])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK2,X1))
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f387,f325])).

fof(f387,plain,
    ( ! [X10] : r1_tarski(k9_relat_1(sK2,X10),u1_struct_0(sK0))
    | ~ spl13_8 ),
    inference(resolution,[],[f384,f163])).

fof(f384,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(k9_relat_1(X2,X3),X1) ) ),
    inference(duplicate_literal_removal,[],[f381])).

fof(f381,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X3),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f375,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',redefinition_k7_relset_1)).

fof(f375,plain,(
    ! [X12,X10,X13,X11] :
      ( r1_tarski(k7_relset_1(X11,X12,X10,X13),X12)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ),
    inference(resolution,[],[f128,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',dt_k7_relset_1)).

fof(f38702,plain,(
    ! [X1630,X1633,X1627,X1629,X1631,X1632,X1628] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1627,k2_zfmisc_1(X1628,k2_zfmisc_1(X1629,sK9(k1_zfmisc_1(X1630))))))),X1631),X1632),X1633)),X1630)
      | v1_xboole_0(X1630)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1627,k2_zfmisc_1(X1628,k2_zfmisc_1(X1629,sK9(k1_zfmisc_1(X1630))))))),X1631),X1632),X1633)) ) ),
    inference(resolution,[],[f17362,f119])).

fof(f17362,plain,(
    ! [X492,X494,X490,X496,X493,X495,X491] :
      ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X490,k2_zfmisc_1(X491,k2_zfmisc_1(X492,sK9(k1_zfmisc_1(X493))))))),X494),X495),X496)),X493)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X490,k2_zfmisc_1(X491,k2_zfmisc_1(X492,sK9(k1_zfmisc_1(X493))))))),X494),X495),X496)) ) ),
    inference(resolution,[],[f10124,f323])).

fof(f10124,plain,(
    ! [X269,X271,X273,X268,X270,X272,X274] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X268,k2_zfmisc_1(X269,k2_zfmisc_1(X270,X271))))),X272),X273),X274)),X271)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X268,k2_zfmisc_1(X269,k2_zfmisc_1(X270,X271))))),X272),X273),X274)) ) ),
    inference(global_subsumption,[],[f588,f10069])).

fof(f10069,plain,(
    ! [X269,X271,X273,X268,X270,X272,X274] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X268,k2_zfmisc_1(X269,k2_zfmisc_1(X270,X271))))),X272),X273),X274)),X271)
      | v1_xboole_0(X271)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X268,k2_zfmisc_1(X269,k2_zfmisc_1(X270,X271))))),X272),X273),X274)) ) ),
    inference(resolution,[],[f10045,f426])).

fof(f426,plain,(
    ! [X12,X13,X11] : m1_subset_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X13),k1_zfmisc_1(X12)) ),
    inference(resolution,[],[f383,f116])).

fof(f383,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | m1_subset_1(k9_relat_1(X6,X7),k1_zfmisc_1(X5)) ) ),
    inference(duplicate_literal_removal,[],[f382])).

fof(f382,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(k9_relat_1(X6,X7),k1_zfmisc_1(X5))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(superposition,[],[f128,f129])).

fof(f10045,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | r2_hidden(sK9(k9_relat_1(k9_relat_1(X3,X4),X5)),X2)
      | v1_xboole_0(X2)
      | v1_xboole_0(k9_relat_1(k9_relat_1(X3,X4),X5)) ) ),
    inference(duplicate_literal_removal,[],[f10044])).

fof(f10044,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k9_relat_1(k9_relat_1(X3,X4),X5))
      | r2_hidden(sK9(k9_relat_1(k9_relat_1(X3,X4),X5)),X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(superposition,[],[f10043,f129])).

fof(f10043,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,X2),X3,X4),X5))
      | r2_hidden(sK9(k9_relat_1(k9_relat_1(X3,X4),X5)),X2)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(duplicate_literal_removal,[],[f10042])).

fof(f10042,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(X3,X4),X5)),X2)
      | v1_xboole_0(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,X2),X3,X4),X5))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(superposition,[],[f4806,f129])).

fof(f4806,plain,(
    ! [X441,X443,X444,X440,X442,X439] :
      ( r2_hidden(sK9(k9_relat_1(k7_relset_1(X440,k2_zfmisc_1(X441,X442),X439,X443),X444)),X442)
      | v1_xboole_0(k9_relat_1(k7_relset_1(X440,k2_zfmisc_1(X441,X442),X439,X443),X444))
      | v1_xboole_0(X442)
      | ~ m1_subset_1(X439,k1_zfmisc_1(k2_zfmisc_1(X440,k2_zfmisc_1(X441,X442)))) ) ),
    inference(resolution,[],[f1335,f119])).

fof(f1335,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK9(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,X2),X3,X4),X5)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | v1_xboole_0(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,X2),X3,X4),X5)) ) ),
    inference(resolution,[],[f464,f277])).

fof(f464,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(k7_relset_1(X2,k2_zfmisc_1(X3,X1),X4,X5),X6))
      | m1_subset_1(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,k2_zfmisc_1(X3,X1)))) ) ),
    inference(resolution,[],[f448,f375])).

fof(f448,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | m1_subset_1(X3,X2)
      | ~ r2_hidden(X3,k9_relat_1(X0,X4)) ) ),
    inference(resolution,[],[f423,f126])).

fof(f423,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k9_relat_1(X0,X1),k1_zfmisc_1(X2))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,X2)) ) ),
    inference(resolution,[],[f383,f123])).

fof(f588,plain,(
    ! [X14,X12,X17,X15,X13,X11,X16] :
      ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X12,k2_zfmisc_1(X13,k2_zfmisc_1(X14,X11))))),X15),X16),X17))
      | ~ v1_xboole_0(X11) ) ),
    inference(resolution,[],[f585,f417])).

fof(f417,plain,(
    ! [X6,X10,X8,X7,X9] : r1_tarski(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X6,k2_zfmisc_1(X7,X8)))),X9),X10),X8) ),
    inference(resolution,[],[f385,f388])).

fof(f388,plain,(
    ! [X12,X13,X11] : r1_tarski(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X11,X12))),X13),X12) ),
    inference(resolution,[],[f384,f116])).

fof(f385,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
      | r1_tarski(k9_relat_1(X0,X1),X2) ) ),
    inference(resolution,[],[f384,f123])).

fof(f585,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X2,X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k9_relat_1(X1,X3)) ) ),
    inference(duplicate_literal_removal,[],[f576])).

fof(f576,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r1_tarski(X1,k2_zfmisc_1(X2,X0))
      | v1_xboole_0(k9_relat_1(X1,X3))
      | ~ r1_tarski(X1,k2_zfmisc_1(X2,X0)) ) ),
    inference(resolution,[],[f509,f123])).

fof(f509,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | v1_xboole_0(k9_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f500,f129])).

fof(f500,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(k7_relset_1(X1,X0,X2,X3))
      | ~ v1_xboole_0(X0)
      | ~ r1_tarski(X2,k2_zfmisc_1(X1,X0)) ) ),
    inference(resolution,[],[f488,f123])).

fof(f488,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(k7_relset_1(X2,X0,X1,X3)) ) ),
    inference(resolution,[],[f374,f277])).

fof(f374,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(X8,k7_relset_1(X6,X7,X5,X9))
      | ~ v1_xboole_0(X7)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ) ),
    inference(resolution,[],[f128,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t5_subset)).

fof(f59945,plain,
    ( spl13_56
    | spl13_160
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f59939,f162,f59943,f393])).

fof(f59943,plain,
    ( spl13_160
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( v1_xboole_0(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2)))),X3,X4),X5))
        | r2_hidden(sK9(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2)))),X3,X4),X5)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_160])])).

fof(f59939,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_xboole_0(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2)))),X3,X4),X5))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2)))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2)))),X3,X4),X5)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f59122,f119])).

fof(f59122,plain,
    ( ! [X580,X582,X578,X581,X577,X579] :
        ( m1_subset_1(sK9(k9_relat_1(k7_relset_1(X578,k2_zfmisc_1(X579,sK9(k1_zfmisc_1(k9_relat_1(sK2,X577)))),X580,X581),X582)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k7_relset_1(X578,k2_zfmisc_1(X579,sK9(k1_zfmisc_1(k9_relat_1(sK2,X577)))),X580,X581),X582))
        | ~ m1_subset_1(X580,k1_zfmisc_1(k2_zfmisc_1(X578,k2_zfmisc_1(X579,sK9(k1_zfmisc_1(k9_relat_1(sK2,X577)))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X577)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9333,f390])).

fof(f9333,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( r2_hidden(sK9(k9_relat_1(k7_relset_1(X7,k2_zfmisc_1(X8,sK9(k1_zfmisc_1(X6))),X9,X10),X11)),X6)
      | v1_xboole_0(sK9(k1_zfmisc_1(X6)))
      | v1_xboole_0(k9_relat_1(k7_relset_1(X7,k2_zfmisc_1(X8,sK9(k1_zfmisc_1(X6))),X9,X10),X11))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,k2_zfmisc_1(X8,sK9(k1_zfmisc_1(X6)))))) ) ),
    inference(resolution,[],[f9331,f375])).

fof(f9331,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X3,sK9(k1_zfmisc_1(X2))))
      | v1_xboole_0(sK9(k1_zfmisc_1(X2)))
      | r2_hidden(sK9(k9_relat_1(X0,X1)),X2)
      | v1_xboole_0(k9_relat_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f9272])).

fof(f9272,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(k9_relat_1(X0,X1)),X2)
      | v1_xboole_0(sK9(k1_zfmisc_1(X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,sK9(k1_zfmisc_1(X2))))
      | v1_xboole_0(k9_relat_1(X0,X1))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,sK9(k1_zfmisc_1(X2)))) ) ),
    inference(resolution,[],[f9271,f123])).

fof(f9271,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(X1)))))
      | r2_hidden(sK9(k9_relat_1(X2,X3)),X1)
      | v1_xboole_0(sK9(k1_zfmisc_1(X1)))
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,sK9(k1_zfmisc_1(X1))))
      | v1_xboole_0(k9_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f9212,f129])).

fof(f9212,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(k7_relset_1(X3,sK9(k1_zfmisc_1(X2)),X0,X1))
      | r2_hidden(sK9(k9_relat_1(X0,X1)),X2)
      | v1_xboole_0(sK9(k1_zfmisc_1(X2)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,sK9(k1_zfmisc_1(X2)))) ) ),
    inference(resolution,[],[f9211,f123])).

fof(f9211,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(X1)))))
      | r2_hidden(sK9(k9_relat_1(X2,X3)),X1)
      | v1_xboole_0(k7_relset_1(X0,sK9(k1_zfmisc_1(X1)),X2,X3))
      | v1_xboole_0(sK9(k1_zfmisc_1(X1))) ) ),
    inference(global_subsumption,[],[f320,f9209])).

fof(f9209,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(k9_relat_1(X2,X3)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(X1)))))
      | v1_xboole_0(k7_relset_1(X0,sK9(k1_zfmisc_1(X1)),X2,X3))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK9(k1_zfmisc_1(X1))) ) ),
    inference(duplicate_literal_removal,[],[f9208])).

fof(f9208,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(k9_relat_1(X2,X3)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(X1)))))
      | v1_xboole_0(k7_relset_1(X0,sK9(k1_zfmisc_1(X1)),X2,X3))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK9(k1_zfmisc_1(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(X1))))) ) ),
    inference(superposition,[],[f4559,f129])).

fof(f4559,plain,(
    ! [X335,X337,X336,X338] :
      ( r2_hidden(sK9(k7_relset_1(X337,sK9(k1_zfmisc_1(X335)),X336,X338)),X335)
      | ~ m1_subset_1(X336,k1_zfmisc_1(k2_zfmisc_1(X337,sK9(k1_zfmisc_1(X335)))))
      | v1_xboole_0(k7_relset_1(X337,sK9(k1_zfmisc_1(X335)),X336,X338))
      | v1_xboole_0(X335)
      | v1_xboole_0(sK9(k1_zfmisc_1(X335))) ) ),
    inference(resolution,[],[f1301,f119])).

fof(f1301,plain,(
    ! [X101,X99,X102,X100] :
      ( m1_subset_1(sK9(k7_relset_1(X99,sK9(k1_zfmisc_1(X100)),X101,X102)),X100)
      | v1_xboole_0(sK9(k1_zfmisc_1(X100)))
      | ~ m1_subset_1(X101,k1_zfmisc_1(k2_zfmisc_1(X99,sK9(k1_zfmisc_1(X100)))))
      | v1_xboole_0(k7_relset_1(X99,sK9(k1_zfmisc_1(X100)),X101,X102)) ) ),
    inference(resolution,[],[f779,f323])).

fof(f779,plain,(
    ! [X76,X74,X77,X75] :
      ( r2_hidden(sK9(k7_relset_1(X75,X76,X74,X77)),X76)
      | v1_xboole_0(k7_relset_1(X75,X76,X74,X77))
      | v1_xboole_0(X76)
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(X75,X76))) ) ),
    inference(resolution,[],[f535,f119])).

fof(f535,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(k7_relset_1(X0,X1,X2,X3)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3)) ) ),
    inference(resolution,[],[f373,f277])).

fof(f373,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k7_relset_1(X1,X2,X0,X4))
      | m1_subset_1(X3,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f128,f126])).

fof(f320,plain,(
    ! [X0] :
      ( v1_xboole_0(sK9(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f307,f277])).

fof(f307,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK9(k1_zfmisc_1(X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f127,f116])).

fof(f54907,plain,
    ( spl13_56
    | spl13_158
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f54901,f162,f54905,f393])).

fof(f54905,plain,
    ( spl13_158
  <=> ! [X1,X3,X5,X7,X0,X2,X4,X6] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))))))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))),X0,X5),X6),X7)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))),X0,X5),X6),X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_158])])).

fof(f54901,plain,
    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))))))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))),X0,X5),X6),X7))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))),X0,X5),X6),X7)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f53003,f119])).

fof(f53003,plain,
    ( ! [X670,X673,X675,X669,X671,X676,X672,X674] :
        ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(k7_relset_1(X669,k2_zfmisc_1(X670,k2_zfmisc_1(X671,k9_relat_1(sK2,X672))),X673,X674),X675),X676)),u1_struct_0(sK0))
        | ~ m1_subset_1(X673,k1_zfmisc_1(k2_zfmisc_1(X669,k2_zfmisc_1(X670,k2_zfmisc_1(X671,k9_relat_1(sK2,X672))))))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k7_relset_1(X669,k2_zfmisc_1(X670,k2_zfmisc_1(X671,k9_relat_1(sK2,X672))),X673,X674),X675),X676)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f10105,f390])).

fof(f10105,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k7_relset_1(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17)),X18,X19),X20),X21)),X17)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k7_relset_1(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17)),X18,X19),X20),X21))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17))))) ) ),
    inference(global_subsumption,[],[f664,f10048])).

fof(f10048,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k7_relset_1(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17)),X18,X19),X20),X21)),X17)
      | v1_xboole_0(X17)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k7_relset_1(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17)),X18,X19),X20),X21))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17))))) ) ),
    inference(resolution,[],[f10045,f128])).

fof(f664,plain,(
    ! [X14,X21,X19,X17,X15,X20,X18,X16] :
      ( v1_xboole_0(k9_relat_1(k9_relat_1(k7_relset_1(X15,k2_zfmisc_1(X16,k2_zfmisc_1(X17,X18)),X14,X19),X20),X21))
      | ~ v1_xboole_0(X18)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X15,k2_zfmisc_1(X16,k2_zfmisc_1(X17,X18))))) ) ),
    inference(resolution,[],[f386,f585])).

fof(f386,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( r1_tarski(k9_relat_1(k7_relset_1(X4,k2_zfmisc_1(X5,X6),X7,X8),X9),X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X4,k2_zfmisc_1(X5,X6)))) ) ),
    inference(resolution,[],[f384,f128])).

fof(f52396,plain,
    ( spl13_56
    | spl13_156
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f52390,f162,f52394,f393])).

fof(f52394,plain,
    ( spl13_156
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))))))
        | r2_hidden(sK9(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))),X0,X4),X5)),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3))),k9_relat_1(X0,X4),X5))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X3))))
        | v1_xboole_0(k9_relat_1(sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_156])])).

fof(f52390,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))))))
        | v1_xboole_0(k9_relat_1(sK2,X3))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X3))))
        | v1_xboole_0(k7_relset_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3))),k9_relat_1(X0,X4),X5))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,sK9(k1_zfmisc_1(k9_relat_1(sK2,X3)))),X0,X4),X5)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f51918,f119])).

fof(f51918,plain,
    ( ! [X580,X582,X578,X581,X577,X579] :
        ( m1_subset_1(sK9(k9_relat_1(k7_relset_1(X582,k2_zfmisc_1(X577,sK9(k1_zfmisc_1(k9_relat_1(sK2,X578)))),X579,X580),X581)),u1_struct_0(sK0))
        | ~ m1_subset_1(X579,k1_zfmisc_1(k2_zfmisc_1(X582,k2_zfmisc_1(X577,sK9(k1_zfmisc_1(k9_relat_1(sK2,X578)))))))
        | v1_xboole_0(k9_relat_1(sK2,X578))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X578))))
        | v1_xboole_0(k7_relset_1(X577,sK9(k1_zfmisc_1(k9_relat_1(sK2,X578))),k9_relat_1(X579,X580),X581)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f36693,f390])).

fof(f36693,plain,(
    ! [X1416,X1412,X1414,X1411,X1413,X1415] :
      ( r2_hidden(sK9(k9_relat_1(k7_relset_1(X1416,k2_zfmisc_1(X1412,sK9(k1_zfmisc_1(X1411))),X1413,X1414),X1415)),X1411)
      | v1_xboole_0(k7_relset_1(X1412,sK9(k1_zfmisc_1(X1411)),k9_relat_1(X1413,X1414),X1415))
      | ~ m1_subset_1(X1413,k1_zfmisc_1(k2_zfmisc_1(X1416,k2_zfmisc_1(X1412,sK9(k1_zfmisc_1(X1411))))))
      | v1_xboole_0(X1411)
      | v1_xboole_0(sK9(k1_zfmisc_1(X1411))) ) ),
    inference(resolution,[],[f7896,f119])).

fof(f7896,plain,(
    ! [X325,X327,X323,X324,X326,X322] :
      ( m1_subset_1(sK9(k9_relat_1(k7_relset_1(X323,k2_zfmisc_1(X324,sK9(k1_zfmisc_1(X325))),X322,X326),X327)),X325)
      | v1_xboole_0(sK9(k1_zfmisc_1(X325)))
      | v1_xboole_0(k7_relset_1(X324,sK9(k1_zfmisc_1(X325)),k9_relat_1(X322,X326),X327))
      | ~ m1_subset_1(X322,k1_zfmisc_1(k2_zfmisc_1(X323,k2_zfmisc_1(X324,sK9(k1_zfmisc_1(X325)))))) ) ),
    inference(resolution,[],[f7806,f323])).

fof(f7806,plain,(
    ! [X524,X526,X522,X525,X527,X523] :
      ( r2_hidden(sK9(k9_relat_1(k7_relset_1(X527,k2_zfmisc_1(X522,X523),X524,X525),X526)),X523)
      | ~ m1_subset_1(X524,k1_zfmisc_1(k2_zfmisc_1(X527,k2_zfmisc_1(X522,X523))))
      | v1_xboole_0(X523)
      | v1_xboole_0(k7_relset_1(X522,X523,k9_relat_1(X524,X525),X526)) ) ),
    inference(resolution,[],[f7748,f119])).

fof(f7748,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK9(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,X2),X3,X4),X5)),X2)
      | v1_xboole_0(k7_relset_1(X1,X2,k9_relat_1(X3,X4),X5))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(duplicate_literal_removal,[],[f7746])).

fof(f7746,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k7_relset_1(X1,X2,k9_relat_1(X3,X4),X5))
      | m1_subset_1(sK9(k9_relat_1(k7_relset_1(X0,k2_zfmisc_1(X1,X2),X3,X4),X5)),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(superposition,[],[f784,f129])).

fof(f784,plain,(
    ! [X14,X12,X10,X15,X13,X11] :
      ( v1_xboole_0(k7_relset_1(X11,X12,k7_relset_1(X10,k2_zfmisc_1(X11,X12),X13,X14),X15))
      | m1_subset_1(sK9(k9_relat_1(k7_relset_1(X10,k2_zfmisc_1(X11,X12),X13,X14),X15)),X12)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X10,k2_zfmisc_1(X11,X12)))) ) ),
    inference(resolution,[],[f781,f128])).

fof(f781,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK9(k9_relat_1(X2,X3)),X1)
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f780])).

fof(f780,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(k9_relat_1(X2,X3)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f535,f129])).

fof(f52387,plain,
    ( spl13_56
    | spl13_154
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f52381,f162,f52385,f393])).

fof(f52385,plain,
    ( spl13_154
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4)))),X5)),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4)))),X5))
        | v1_xboole_0(k9_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_154])])).

fof(f52381,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4)))),X5))
        | v1_xboole_0(k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4)))),X5)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f51625,f119])).

fof(f51625,plain,
    ( ! [X553,X555,X551,X556,X552,X554] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X555,k7_relset_1(X551,k9_relat_1(sK2,X552),X553,X554)))),X556)),u1_struct_0(sK0))
        | ~ m1_subset_1(X553,k1_zfmisc_1(k2_zfmisc_1(X551,k9_relat_1(sK2,X552))))
        | v1_xboole_0(k9_relat_1(sK2,X552))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X555,k7_relset_1(X551,k9_relat_1(sK2,X552),X553,X554)))),X556))
        | v1_xboole_0(k7_relset_1(X551,k9_relat_1(sK2,X552),X553,X554)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f36270,f390])).

fof(f36270,plain,(
    ! [X1416,X1412,X1414,X1411,X1413,X1415] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1411,k7_relset_1(X1412,X1413,X1414,X1415)))),X1416)),X1413)
      | v1_xboole_0(k7_relset_1(X1412,X1413,X1414,X1415))
      | ~ m1_subset_1(X1414,k1_zfmisc_1(k2_zfmisc_1(X1412,X1413)))
      | v1_xboole_0(X1413)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1411,k7_relset_1(X1412,X1413,X1414,X1415)))),X1416)) ) ),
    inference(resolution,[],[f885,f119])).

fof(f885,plain,(
    ! [X14,X12,X10,X13,X11,X9] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X13,k7_relset_1(X9,X10,X11,X12)))),X14)),X10)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X13,k7_relset_1(X9,X10,X11,X12)))),X14))
      | v1_xboole_0(k7_relset_1(X9,X10,X11,X12))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) ) ),
    inference(resolution,[],[f661,f373])).

fof(f661,plain,(
    ! [X50,X48,X49] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X48,X49))),X50)),X49)
      | v1_xboole_0(X49)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X48,X49))),X50)) ) ),
    inference(resolution,[],[f459,f119])).

fof(f459,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)),X1)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),X2)) ) ),
    inference(resolution,[],[f404,f277])).

fof(f404,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,X2))),X3))
      | m1_subset_1(X0,X2) ) ),
    inference(resolution,[],[f388,f325])).

fof(f51861,plain,
    ( spl13_56
    | spl13_152
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f51857,f162,f51859,f393])).

fof(f51859,plain,
    ( spl13_152
  <=> ! [X1,X3,X0,X2,X4] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))),X3)))),X4)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))),X3))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))),X3)))),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_152])])).

fof(f51857,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))),X3)))),X4))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))),X3))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))),X3)))),X4)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f51766,f119])).

fof(f51766,plain,
    ( ! [X528,X530,X529,X531,X527] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X530,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X527,k9_relat_1(sK2,X528)))),X529)))),X531)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X528))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X530,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X527,k9_relat_1(sK2,X528)))),X529)))),X531))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X527,k9_relat_1(sK2,X528)))),X529)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f36432,f390])).

fof(f36432,plain,(
    ! [X1262,X1260,X1259,X1263,X1261] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1259,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1260,X1261))),X1262)))),X1263)),X1261)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1260,X1261))),X1262))
      | v1_xboole_0(X1261)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1259,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1260,X1261))),X1262)))),X1263)) ) ),
    inference(resolution,[],[f888,f119])).

fof(f888,plain,(
    ! [X28,X26,X24,X27,X25] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X27,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X26)))),X28)),X25)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X27,k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X26)))),X28))
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X24,X25))),X26)) ) ),
    inference(resolution,[],[f661,f404])).

fof(f47294,plain,
    ( spl13_56
    | spl13_150
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f47290,f162,f47292,f393])).

fof(f47292,plain,
    ( spl13_150
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2))
        | v1_xboole_0(k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_150])])).

fof(f47290,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f44778,f119])).

fof(f44778,plain,
    ( ! [X366,X365,X367] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X366,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X365)))))))),X367)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X365)))))
        | v1_xboole_0(k9_relat_1(sK2,X365))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X366,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X365)))))))),X367))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X365)))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f29003,f390])).

fof(f29003,plain,(
    ! [X854,X855,X853] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X853,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X854))))))),X855)),X854)
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X854)))))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X854))))
      | v1_xboole_0(X854)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X853,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X854))))))),X855)) ) ),
    inference(resolution,[],[f897,f119])).

fof(f897,plain,(
    ! [X78,X79,X77] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X78,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X77))))))),X79)),X77)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X78,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X77))))))),X79))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X77)))))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X77)))) ) ),
    inference(resolution,[],[f661,f359])).

fof(f359,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | m1_subset_1(X1,X0)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X0)))) ) ),
    inference(resolution,[],[f326,f126])).

fof(f46674,plain,
    ( spl13_56
    | spl13_148
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f46670,f162,f46672,f393])).

fof(f46672,plain,
    ( spl13_148
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))))),X2))
        | r2_hidden(sK9(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_148])])).

fof(f46670,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))))),X2))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f46585,f119])).

fof(f46585,plain,
    ( ! [X377,X376,X375] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X376,sK9(k1_zfmisc_1(k9_relat_1(sK2,X375)))))))),X377)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X376,sK9(k1_zfmisc_1(k9_relat_1(sK2,X375)))))))),X377))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X376,sK9(k1_zfmisc_1(k9_relat_1(sK2,X375))))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X375)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9353,f390])).

fof(f9353,plain,(
    ! [X167,X165,X166] :
      ( r2_hidden(sK9(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X166,sK9(k1_zfmisc_1(X165))))))),X167)),X165)
      | v1_xboole_0(sK9(k1_zfmisc_1(X165)))
      | v1_xboole_0(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X166,sK9(k1_zfmisc_1(X165))))))),X167))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X166,sK9(k1_zfmisc_1(X165))))))) ) ),
    inference(resolution,[],[f9331,f361])).

fof(f361,plain,(
    ! [X4] :
      ( r1_tarski(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X4)))),X4)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X4)))) ) ),
    inference(resolution,[],[f326,f122])).

fof(f45841,plain,
    ( spl13_56
    | spl13_146
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f45837,f162,f45839,f393])).

fof(f45839,plain,
    ( spl13_146
  <=> ! [X1,X3,X0,X2,X4] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k9_relat_1(sK2,X2)))))))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))))),X3),X4)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))))),X3),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_146])])).

fof(f45837,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k9_relat_1(sK2,X2)))))))
        | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))))),X3),X4))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))))),X3),X4)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f45752,f119])).

fof(f45752,plain,
    ( ! [X455,X457,X459,X456,X458] :
        ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X455,k2_zfmisc_1(X456,k9_relat_1(sK2,X457))))))),X458),X459)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X455,k2_zfmisc_1(X456,k9_relat_1(sK2,X457)))))))
        | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X455,k2_zfmisc_1(X456,k9_relat_1(sK2,X457))))))),X458),X459)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f10133,f390])).

fof(f10133,plain,(
    ! [X356,X352,X354,X353,X355] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X352,k2_zfmisc_1(X353,X354)))))),X355),X356)),X354)
      | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X352,k2_zfmisc_1(X353,X354)))))),X355),X356))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X352,k2_zfmisc_1(X353,X354)))))) ) ),
    inference(global_subsumption,[],[f612,f10079])).

fof(f10079,plain,(
    ! [X356,X352,X354,X353,X355] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X352,k2_zfmisc_1(X353,X354)))))),X355),X356)),X354)
      | v1_xboole_0(X354)
      | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X352,k2_zfmisc_1(X353,X354)))))),X355),X356))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X352,k2_zfmisc_1(X353,X354)))))) ) ),
    inference(resolution,[],[f10045,f326])).

fof(f612,plain,(
    ! [X12,X10,X8,X11,X9] :
      ( v1_xboole_0(k9_relat_1(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X8,k2_zfmisc_1(X9,X10)))))),X11),X12))
      | ~ v1_xboole_0(X10)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X8,k2_zfmisc_1(X9,X10)))))) ) ),
    inference(resolution,[],[f389,f585])).

fof(f389,plain,(
    ! [X14,X15,X16] :
      ( r1_tarski(k9_relat_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X14,X15))))),X16),X15)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k2_zfmisc_1(X14,X15))))) ) ),
    inference(resolution,[],[f384,f326])).

fof(f37922,plain,
    ( spl13_56
    | spl13_144
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f37918,f162,f37920,f393])).

fof(f37920,plain,
    ( spl13_144
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X2)))))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X3))))),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X2)),X0,X3))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X0,X3))))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X3))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_144])])).

fof(f37918,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X2)))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X3)))))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X0,X3))))
        | v1_xboole_0(k7_relset_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X2)),X0,X3))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X3))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f37814,f119])).

fof(f37814,plain,
    ( ! [X377,X379,X380,X378] :
        ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(k9_relat_1(X379,X380))))),u1_struct_0(sK0))
        | ~ m1_subset_1(X379,k1_zfmisc_1(k2_zfmisc_1(X377,k1_zfmisc_1(k9_relat_1(sK2,X378)))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k9_relat_1(X379,X380)))))
        | v1_xboole_0(k9_relat_1(sK2,X378))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X379,X380))))
        | v1_xboole_0(k7_relset_1(X377,k1_zfmisc_1(k9_relat_1(sK2,X378)),X379,X380)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f23999,f390])).

fof(f23999,plain,(
    ! [X912,X911,X913,X910] :
      ( r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k9_relat_1(X910,X911))))),X913)
      | v1_xboole_0(k7_relset_1(X912,k1_zfmisc_1(X913),X910,X911))
      | ~ m1_subset_1(X910,k1_zfmisc_1(k2_zfmisc_1(X912,k1_zfmisc_1(X913))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k9_relat_1(X910,X911)))))
      | v1_xboole_0(X913)
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X910,X911)))) ) ),
    inference(resolution,[],[f7179,f119])).

fof(f7179,plain,(
    ! [X14,X15,X13,X16] :
      ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(k9_relat_1(X15,X16))))),X14)
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X15,X16))))
      | v1_xboole_0(k7_relset_1(X13,k1_zfmisc_1(X14),X15,X16))
      | ~ m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X13,k1_zfmisc_1(X14))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k9_relat_1(X15,X16))))) ) ),
    inference(resolution,[],[f4286,f277])).

fof(f4286,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X3)))))
      | v1_xboole_0(k7_relset_1(X1,k1_zfmisc_1(X2),X0,X3))
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X0,X3))))
      | m1_subset_1(X4,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X2)))) ) ),
    inference(resolution,[],[f4285,f126])).

fof(f4285,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(X2,X3)))),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X2,X3)))) ) ),
    inference(duplicate_literal_removal,[],[f4284])).

fof(f4284,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X2,X3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(X2,X3)))),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f4283,f129])).

fof(f4283,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X0,X1,X2,X3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(X2,X3)))),X1) ) ),
    inference(duplicate_literal_removal,[],[f4282])).

fof(f4282,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(X2,X3)))),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X0,X1,X2,X3))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f536,f129])).

fof(f536,plain,(
    ! [X6,X4,X7,X5] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k7_relset_1(X4,X5,X6,X7)))),X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | v1_xboole_0(k7_relset_1(X4,X5,X6,X7))
      | v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X4,X5,X6,X7)))) ) ),
    inference(resolution,[],[f373,f362])).

fof(f32630,plain,
    ( spl13_56
    | spl13_142
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f32626,f28507,f32628,f393])).

fof(f32628,plain,
    ( spl13_142
  <=> ! [X1,X0,X2] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK7(sK1,sK0,sK2,X0)))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK7(sK1,sK0,sK2,X0)))),X2))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_142])])).

fof(f32626,plain,
    ( ! [X2,X0,X1] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK7(sK1,sK0,sK2,X0)))),X2))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK7(sK1,sK0,sK2,X0)))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28527,f119])).

fof(f28527,plain,
    ( ! [X33,X34,X32] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X33,sK7(sK1,sK0,sK2,X32)))),X34)),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X32)
        | ~ m1_subset_1(X32,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X32),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X32))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X33,sK7(sK1,sK0,sK2,X32)))),X34)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28510,f661])).

fof(f32086,plain,
    ( spl13_56
    | spl13_140
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f32080,f162,f32084,f393])).

fof(f32084,plain,
    ( spl13_140
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK9(k3_funct_2(X0,k1_zfmisc_1(k9_relat_1(sK2,X2)),X1,X3)),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,k1_zfmisc_1(k9_relat_1(sK2,X2)))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(k3_funct_2(X0,k1_zfmisc_1(k9_relat_1(sK2,X2)),X1,X3))
        | ~ m1_subset_1(X3,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X2))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_140])])).

fof(f32080,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X2)))))
        | ~ m1_subset_1(X3,X0)
        | v1_xboole_0(k3_funct_2(X0,k1_zfmisc_1(k9_relat_1(sK2,X2)),X1,X3))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | ~ v1_funct_2(X1,X0,k1_zfmisc_1(k9_relat_1(sK2,X2)))
        | ~ v1_funct_1(X1)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k3_funct_2(X0,k1_zfmisc_1(k9_relat_1(sK2,X2)),X1,X3)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f26841,f119])).

fof(f26841,plain,
    ( ! [X341,X339,X340,X342] :
        ( m1_subset_1(sK9(k3_funct_2(X340,k1_zfmisc_1(k9_relat_1(sK2,X341)),X339,X342)),u1_struct_0(sK0))
        | v1_xboole_0(X340)
        | ~ m1_subset_1(X339,k1_zfmisc_1(k2_zfmisc_1(X340,k1_zfmisc_1(k9_relat_1(sK2,X341)))))
        | ~ m1_subset_1(X342,X340)
        | v1_xboole_0(k3_funct_2(X340,k1_zfmisc_1(k9_relat_1(sK2,X341)),X339,X342))
        | v1_xboole_0(k9_relat_1(sK2,X341))
        | ~ v1_funct_2(X339,X340,k1_zfmisc_1(k9_relat_1(sK2,X341)))
        | ~ v1_funct_1(X339) )
    | ~ spl13_8 ),
    inference(resolution,[],[f18239,f390])).

fof(f18239,plain,(
    ! [X720,X718,X717,X719] :
      ( r2_hidden(sK9(k3_funct_2(X718,k1_zfmisc_1(X719),X717,X720)),X719)
      | ~ v1_funct_1(X717)
      | v1_xboole_0(X718)
      | ~ m1_subset_1(X717,k1_zfmisc_1(k2_zfmisc_1(X718,k1_zfmisc_1(X719))))
      | ~ m1_subset_1(X720,X718)
      | v1_xboole_0(k3_funct_2(X718,k1_zfmisc_1(X719),X717,X720))
      | v1_xboole_0(X719)
      | ~ v1_funct_2(X717,X718,k1_zfmisc_1(X719)) ) ),
    inference(resolution,[],[f4120,f119])).

fof(f4120,plain,(
    ! [X10,X8,X7,X9] :
      ( m1_subset_1(sK9(k3_funct_2(X8,k1_zfmisc_1(X9),X7,X10)),X9)
      | ~ v1_funct_2(X7,X8,k1_zfmisc_1(X9))
      | ~ v1_funct_1(X7)
      | v1_xboole_0(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,k1_zfmisc_1(X9))))
      | ~ m1_subset_1(X10,X8)
      | v1_xboole_0(k3_funct_2(X8,k1_zfmisc_1(X9),X7,X10)) ) ),
    inference(resolution,[],[f685,f277])).

fof(f685,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k3_funct_2(X1,k1_zfmisc_1(X3),X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X3))))
      | ~ v1_funct_2(X2,X1,k1_zfmisc_1(X3))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | m1_subset_1(X4,X3)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f130,f126])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',dt_k3_funct_2)).

fof(f28562,plain,
    ( spl13_56
    | spl13_138
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f28558,f28507,f28560,f393])).

fof(f28560,plain,
    ( spl13_138
  <=> ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0)))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0))))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_138])])).

fof(f28558,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X0)))),u1_struct_0(sK0)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28516,f119])).

fof(f28516,plain,
    ( ! [X12] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X12)))),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X12),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X12))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK7(sK1,sK0,sK2,X12)))) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28510,f362])).

fof(f28554,plain,
    ( spl13_56
    | spl13_136
    | ~ spl13_134 ),
    inference(avatar_split_clause,[],[f28550,f28507,f28552,f393])).

fof(f28552,plain,
    ( spl13_136
  <=> ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | r2_hidden(sK9(sK7(sK1,sK0,sK2,X0)),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_136])])).

fof(f28550,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK1,sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X0),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK7(sK1,sK0,sK2,X0)),u1_struct_0(sK0)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28515,f119])).

fof(f28515,plain,
    ( ! [X11] :
        ( m1_subset_1(sK9(sK7(sK1,sK0,sK2,X11)),u1_struct_0(sK0))
        | r1_tmap_1(sK1,sK0,sK2,X11)
        | ~ m1_subset_1(X11,u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X11),u1_struct_0(sK0))
        | v1_xboole_0(sK7(sK1,sK0,sK2,X11)) )
    | ~ spl13_134 ),
    inference(resolution,[],[f28510,f277])).

fof(f28509,plain,
    ( spl13_70
    | spl13_18
    | ~ spl13_17
    | ~ spl13_15
    | spl13_24
    | ~ spl13_23
    | ~ spl13_21
    | ~ spl13_13
    | ~ spl13_11
    | spl13_134
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f28468,f162,f28507,f166,f173,f201,f208,f215,f180,f187,f194,f1177])).

fof(f1177,plain,
    ( spl13_70
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_70])])).

fof(f28468,plain,
    ( ! [X448] :
        ( ~ m1_subset_1(X448,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X448)
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(k1_funct_1(sK2,X448),u1_struct_0(sK0))
        | r1_tarski(sK7(sK1,sK0,sK2,X448),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f7283,f163])).

fof(f7283,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | r1_tmap_1(X5,X6,X7,X8)
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | v1_xboole_0(u1_struct_0(X5))
      | ~ m1_subset_1(k1_funct_1(X7,X8),u1_struct_0(X6))
      | r1_tarski(sK7(X5,X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(duplicate_literal_removal,[],[f7282])).

fof(f7282,plain,(
    ! [X6,X8,X7,X5] :
      ( r1_tmap_1(X5,X6,X7,X8)
      | ~ m1_subset_1(X8,u1_struct_0(X5))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(X5),u1_struct_0(X6))
      | ~ v1_funct_1(X7)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | v1_xboole_0(u1_struct_0(X5))
      | ~ m1_subset_1(k1_funct_1(X7,X8),u1_struct_0(X6))
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6)
      | r1_tarski(sK7(X5,X6,X7,X8),u1_struct_0(X6)) ) ),
    inference(resolution,[],[f2006,f524])).

fof(f524,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_connsp_2(X8,X9,X10)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | v2_struct_0(X9)
      | r1_tarski(X8,u1_struct_0(X9)) ) ),
    inference(resolution,[],[f120,f122])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',dt_m1_connsp_2)).

fof(f2006,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2,X3),X1,k1_funct_1(X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f2005])).

fof(f2005,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_connsp_2(sK7(X0,X1,X2,X3),X1,k1_funct_1(X2,X3))
      | r1_tmap_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(superposition,[],[f114,f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',redefinition_k3_funct_2)).

fof(f26472,plain,
    ( spl13_56
    | spl13_132
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f26468,f162,f26470,f393])).

fof(f26470,plain,
    ( spl13_132
  <=> ! [X1,X3,X5,X7,X8,X0,X2,X4,X6] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))))))),X5),X6),X7),X8))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))))))),X5),X6),X7),X8)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_132])])).

fof(f26468,plain,
    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))))))),X5),X6),X7),X8))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k2_zfmisc_1(X3,k9_relat_1(sK2,X4))))))),X5),X6),X7),X8)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f13491,f119])).

fof(f13491,plain,
    ( ! [X325,X327,X321,X323,X324,X326,X320,X322,X328] :
        ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X320,k2_zfmisc_1(X321,k2_zfmisc_1(X322,k2_zfmisc_1(X323,k9_relat_1(sK2,X324))))))),X325),X326),X327),X328)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X320,k2_zfmisc_1(X321,k2_zfmisc_1(X322,k2_zfmisc_1(X323,k9_relat_1(sK2,X324))))))),X325),X326),X327),X328)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f13370,f267])).

fof(f267,plain,(
    ! [X0] : r1_tarski(sK9(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f122,f116])).

fof(f13370,plain,
    ( ! [X428,X430,X436,X432,X434,X429,X431,X437,X433,X435] :
        ( ~ r1_tarski(X428,k2_zfmisc_1(X433,k2_zfmisc_1(X434,k2_zfmisc_1(X435,k2_zfmisc_1(X436,k9_relat_1(sK2,X437))))))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X428,X429),X430),X431),X432))
        | m1_subset_1(sK9(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X428,X429),X430),X431),X432)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f10107,f390])).

fof(f10107,plain,(
    ! [X47,X54,X52,X50,X48,X56,X55,X53,X51,X49] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X47,X48),X49),X50),X51)),X52)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X47,X48),X49),X50),X51))
      | ~ r1_tarski(X47,k2_zfmisc_1(X53,k2_zfmisc_1(X54,k2_zfmisc_1(X55,k2_zfmisc_1(X56,X52))))) ) ),
    inference(global_subsumption,[],[f841,f10052])).

fof(f10052,plain,(
    ! [X47,X54,X52,X50,X48,X56,X55,X53,X51,X49] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X47,X48),X49),X50),X51)),X52)
      | v1_xboole_0(X52)
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X47,X48),X49),X50),X51))
      | ~ r1_tarski(X47,k2_zfmisc_1(X53,k2_zfmisc_1(X54,k2_zfmisc_1(X55,k2_zfmisc_1(X56,X52))))) ) ),
    inference(resolution,[],[f10045,f451])).

fof(f451,plain,(
    ! [X14,X19,X17,X15,X18,X16] :
      ( m1_subset_1(k9_relat_1(k9_relat_1(X14,X18),X19),k1_zfmisc_1(X17))
      | ~ r1_tarski(X14,k2_zfmisc_1(X15,k2_zfmisc_1(X16,X17))) ) ),
    inference(resolution,[],[f423,f383])).

fof(f841,plain,(
    ! [X47,X45,X43,X41,X48,X46,X44,X42,X40,X49] :
      ( ~ r1_tarski(X41,k2_zfmisc_1(X46,k2_zfmisc_1(X47,k2_zfmisc_1(X48,k2_zfmisc_1(X49,X40)))))
      | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(k9_relat_1(X41,X42),X43),X44),X45))
      | ~ v1_xboole_0(X40) ) ),
    inference(resolution,[],[f835,f451])).

fof(f835,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(k9_relat_1(k9_relat_1(X3,X4),X5)) ) ),
    inference(duplicate_literal_removal,[],[f834])).

fof(f834,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k9_relat_1(k9_relat_1(X3,X4),X5))
      | ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,X2)))) ) ),
    inference(superposition,[],[f586,f129])).

fof(f586,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_xboole_0(k9_relat_1(k7_relset_1(X1,k2_zfmisc_1(X2,X0),X3,X4),X5))
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,k2_zfmisc_1(X2,X0)))) ) ),
    inference(resolution,[],[f585,f375])).

fof(f26047,plain,
    ( spl13_56
    | spl13_130
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f26041,f162,f26045,f393])).

fof(f26045,plain,
    ( spl13_130
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | r2_hidden(k3_funct_2(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))),X3,X2),u1_struct_0(sK0))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_130])])).

fof(f26041,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(X0)
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | ~ m1_subset_1(X2,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | ~ v1_funct_2(X3,X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | ~ v1_funct_1(X3)
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(k3_funct_2(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))),X3,X2),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f21623,f119])).

fof(f21623,plain,
    ( ! [X313,X315,X312,X314] :
        ( m1_subset_1(k3_funct_2(X313,sK9(k1_zfmisc_1(k9_relat_1(sK2,X314))),X312,X315),u1_struct_0(sK0))
        | v1_xboole_0(X313)
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X314))))
        | ~ m1_subset_1(X315,X313)
        | ~ m1_subset_1(X312,k1_zfmisc_1(k2_zfmisc_1(X313,sK9(k1_zfmisc_1(k9_relat_1(sK2,X314))))))
        | v1_xboole_0(k9_relat_1(sK2,X314))
        | ~ v1_funct_2(X312,X313,sK9(k1_zfmisc_1(k9_relat_1(sK2,X314))))
        | ~ v1_funct_1(X312) )
    | ~ spl13_8 ),
    inference(resolution,[],[f14516,f390])).

fof(f14516,plain,(
    ! [X629,X631,X628,X630] :
      ( r2_hidden(k3_funct_2(X629,sK9(k1_zfmisc_1(X630)),X628,X631),X630)
      | ~ v1_funct_1(X628)
      | v1_xboole_0(X629)
      | v1_xboole_0(sK9(k1_zfmisc_1(X630)))
      | ~ m1_subset_1(X631,X629)
      | ~ m1_subset_1(X628,k1_zfmisc_1(k2_zfmisc_1(X629,sK9(k1_zfmisc_1(X630)))))
      | v1_xboole_0(X630)
      | ~ v1_funct_2(X628,X629,sK9(k1_zfmisc_1(X630))) ) ),
    inference(resolution,[],[f2204,f119])).

fof(f2204,plain,(
    ! [X134,X132,X135,X133] :
      ( m1_subset_1(k3_funct_2(X133,sK9(k1_zfmisc_1(X134)),X132,X135),X134)
      | ~ v1_funct_2(X132,X133,sK9(k1_zfmisc_1(X134)))
      | ~ v1_funct_1(X132)
      | v1_xboole_0(X133)
      | v1_xboole_0(sK9(k1_zfmisc_1(X134)))
      | ~ m1_subset_1(X135,X133)
      | ~ m1_subset_1(X132,k1_zfmisc_1(k2_zfmisc_1(X133,sK9(k1_zfmisc_1(X134))))) ) ),
    inference(resolution,[],[f696,f323])).

fof(f696,plain,(
    ! [X68,X66,X69,X67] :
      ( r2_hidden(k3_funct_2(X67,X69,X68,X66),X69)
      | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X67,X69)))
      | ~ v1_funct_2(X68,X67,X69)
      | ~ v1_funct_1(X68)
      | v1_xboole_0(X67)
      | v1_xboole_0(X69)
      | ~ m1_subset_1(X66,X67) ) ),
    inference(resolution,[],[f130,f119])).

fof(f25052,plain,
    ( spl13_56
    | spl13_128
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f25048,f162,f25050,f393])).

fof(f25050,plain,
    ( spl13_128
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k9_relat_1(X0,X4)))),X5)),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k9_relat_1(X0,X4)))),X5))
        | v1_xboole_0(k9_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_128])])).

fof(f25048,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k9_relat_1(X0,X4)))),X5))
        | v1_xboole_0(k7_relset_1(X1,k9_relat_1(sK2,X2),X0,X4))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,k9_relat_1(X0,X4)))),X5)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f24959,f119])).

fof(f24959,plain,
    ( ! [X420,X422,X424,X421,X423,X419] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X423,k9_relat_1(X421,X422)))),X424)),u1_struct_0(sK0))
        | ~ m1_subset_1(X421,k1_zfmisc_1(k2_zfmisc_1(X419,k9_relat_1(sK2,X420))))
        | v1_xboole_0(k9_relat_1(sK2,X420))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X423,k9_relat_1(X421,X422)))),X424))
        | v1_xboole_0(k7_relset_1(X419,k9_relat_1(sK2,X420),X421,X422)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f17755,f390])).

fof(f17755,plain,(
    ! [X947,X945,X946,X944,X948,X943] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X943,k9_relat_1(X944,X945)))),X946)),X948)
      | v1_xboole_0(k7_relset_1(X947,X948,X944,X945))
      | ~ m1_subset_1(X944,k1_zfmisc_1(k2_zfmisc_1(X947,X948)))
      | v1_xboole_0(X948)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X943,k9_relat_1(X944,X945)))),X946)) ) ),
    inference(resolution,[],[f7252,f119])).

fof(f7252,plain,(
    ! [X222,X227,X225,X223,X226,X224] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X226,k9_relat_1(X224,X225)))),X227)),X223)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X226,k9_relat_1(X224,X225)))),X227))
      | v1_xboole_0(k7_relset_1(X222,X223,X224,X225))
      | ~ m1_subset_1(X224,k1_zfmisc_1(k2_zfmisc_1(X222,X223))) ) ),
    inference(resolution,[],[f7231,f267])).

fof(f7231,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X5,k9_relat_1(X2,X3)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(k9_relat_1(X4,X6))
      | m1_subset_1(sK9(k9_relat_1(X4,X6)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f7230])).

fof(f7230,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X5,k9_relat_1(X2,X3)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(k9_relat_1(X4,X6))
      | m1_subset_1(sK9(k9_relat_1(X4,X6)),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f1045,f129])).

fof(f1045,plain,(
    ! [X14,X12,X17,X15,X13,X18,X16] :
      ( ~ r1_tarski(X12,k2_zfmisc_1(X18,k7_relset_1(X14,X15,X16,X17)))
      | v1_xboole_0(k7_relset_1(X14,X15,X16,X17))
      | v1_xboole_0(k9_relat_1(X12,X13))
      | m1_subset_1(sK9(k9_relat_1(X12,X13)),X15)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X14,X15))) ) ),
    inference(resolution,[],[f1030,f373])).

fof(f1030,plain,(
    ! [X103,X105,X106,X104] :
      ( r2_hidden(sK9(k9_relat_1(X103,X106)),X105)
      | v1_xboole_0(k9_relat_1(X103,X106))
      | v1_xboole_0(X105)
      | ~ r1_tarski(X103,k2_zfmisc_1(X104,X105)) ) ),
    inference(resolution,[],[f1013,f119])).

fof(f1013,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(k9_relat_1(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
      | v1_xboole_0(k9_relat_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f995])).

fof(f995,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(k9_relat_1(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,X2))
      | v1_xboole_0(k9_relat_1(X0,X1))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,X2)) ) ),
    inference(resolution,[],[f801,f123])).

fof(f801,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(sK9(k9_relat_1(X2,X3)),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | v1_xboole_0(k9_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f782,f129])).

fof(f782,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(k7_relset_1(X3,X2,X0,X1))
      | m1_subset_1(sK9(k9_relat_1(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,X2)) ) ),
    inference(resolution,[],[f781,f123])).

fof(f20784,plain,
    ( spl13_56
    | spl13_126
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f20778,f162,f20782,f393])).

fof(f20782,plain,
    ( spl13_126
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(sK9(k7_relset_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)),X2,X3)))
        | r2_hidden(sK9(sK9(k7_relset_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)),X2,X3))),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)))))
        | v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)),X2,X3))
        | v1_xboole_0(k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_126])])).

fof(f20778,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(sK9(k7_relset_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)),X2,X3)))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)),X2,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k7_relset_1(X0,k1_zfmisc_1(k9_relat_1(sK2,X1)),X2,X3))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f15514,f119])).

fof(f15514,plain,
    ( ! [X269,X271,X268,X270] :
        ( m1_subset_1(sK9(sK9(k7_relset_1(X269,k1_zfmisc_1(k9_relat_1(sK2,X270)),X268,X271))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k7_relset_1(X269,k1_zfmisc_1(k9_relat_1(sK2,X270)),X268,X271)))
        | v1_xboole_0(k9_relat_1(sK2,X270))
        | v1_xboole_0(k7_relset_1(X269,k1_zfmisc_1(k9_relat_1(sK2,X270)),X268,X271))
        | ~ m1_subset_1(X268,k1_zfmisc_1(k2_zfmisc_1(X269,k1_zfmisc_1(k9_relat_1(sK2,X270))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f8415,f390])).

fof(f8415,plain,(
    ! [X449,X451,X452,X450] :
      ( r2_hidden(sK9(sK9(k7_relset_1(X449,k1_zfmisc_1(X450),X451,X452))),X450)
      | ~ m1_subset_1(X451,k1_zfmisc_1(k2_zfmisc_1(X449,k1_zfmisc_1(X450))))
      | v1_xboole_0(sK9(k7_relset_1(X449,k1_zfmisc_1(X450),X451,X452)))
      | v1_xboole_0(X450)
      | v1_xboole_0(k7_relset_1(X449,k1_zfmisc_1(X450),X451,X452)) ) ),
    inference(resolution,[],[f2368,f119])).

fof(f2368,plain,(
    ! [X10,X8,X7,X9] :
      ( m1_subset_1(sK9(sK9(k7_relset_1(X7,k1_zfmisc_1(X8),X9,X10))),X8)
      | v1_xboole_0(k7_relset_1(X7,k1_zfmisc_1(X8),X9,X10))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,k1_zfmisc_1(X8))))
      | v1_xboole_0(sK9(k7_relset_1(X7,k1_zfmisc_1(X8),X9,X10))) ) ),
    inference(resolution,[],[f767,f277])).

fof(f767,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,sK9(k7_relset_1(X1,k1_zfmisc_1(X2),X0,X3)))
      | v1_xboole_0(k7_relset_1(X1,k1_zfmisc_1(X2),X0,X3))
      | m1_subset_1(X4,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(X2)))) ) ),
    inference(resolution,[],[f535,f126])).

fof(f18136,plain,
    ( spl13_56
    | spl13_124
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f18132,f162,f18134,f393])).

fof(f18134,plain,
    ( spl13_124
  <=> ! [X0] :
        ( v1_xboole_0(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | r2_hidden(sK9(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))
        | v1_xboole_0(k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_124])])).

fof(f18132,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f12696,f119])).

fof(f12696,plain,
    ( ! [X171] :
        ( m1_subset_1(sK9(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X171)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X171))))))))
        | v1_xboole_0(k9_relat_1(sK2,X171))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X171)))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X171)))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f6959,f390])).

fof(f6959,plain,(
    ! [X219] :
      ( r2_hidden(sK9(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X219))))))),X219)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X219)))))
      | v1_xboole_0(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X219)))))))
      | v1_xboole_0(X219)
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X219)))))) ) ),
    inference(resolution,[],[f2067,f119])).

fof(f2067,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))))),X0)
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))
      | v1_xboole_0(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))))) ) ),
    inference(resolution,[],[f711,f277])).

fof(f711,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0)))))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))))
      | m1_subset_1(X1,X0)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f510,f126])).

fof(f510,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))),X0)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))) ) ),
    inference(resolution,[],[f359,f277])).

fof(f18116,plain,
    ( spl13_56
    | spl13_122
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f18112,f162,f18114,f393])).

fof(f18114,plain,
    ( spl13_122
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_122])])).

fof(f18112,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f18064,f119])).

fof(f18064,plain,
    ( ! [X251,X249,X250] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X250,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X249)))))))),X251)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X249))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X250,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X249)))))))),X251))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X249)))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f11029,f390])).

fof(f11029,plain,(
    ! [X455,X457,X456] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X455,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X456))))))),X457)),X456)
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X456)))))
      | v1_xboole_0(X456)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X455,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X456))))))),X457)) ) ),
    inference(resolution,[],[f9399,f119])).

fof(f9399,plain,(
    ! [X241,X239,X240] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X240,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X239))))))),X241)),X239)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X240,sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X239))))))),X241))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X239))))) ) ),
    inference(resolution,[],[f9352,f323])).

fof(f9352,plain,(
    ! [X163,X164,X162] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X163,sK9(k1_zfmisc_1(X162))))),X164)),X162)
      | v1_xboole_0(sK9(k1_zfmisc_1(X162)))
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X163,sK9(k1_zfmisc_1(X162))))),X164)) ) ),
    inference(resolution,[],[f9331,f267])).

fof(f17882,plain,
    ( spl13_56
    | spl13_120
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f17878,f162,f17880,f393])).

fof(f17880,plain,
    ( spl13_120
  <=> ! [X1,X3,X0,X2,X4] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))))),X3),X4))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))))),X3),X4)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X2)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_120])])).

fof(f17878,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))))),X3),X4))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X2))))))),X3),X4)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f17831,f119])).

fof(f17831,plain,
    ( ! [X308,X310,X309,X311,X307] :
        ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X308,k2_zfmisc_1(X309,sK9(k1_zfmisc_1(k9_relat_1(sK2,X307))))))),X310),X311)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X308,k2_zfmisc_1(X309,sK9(k1_zfmisc_1(k9_relat_1(sK2,X307))))))),X310),X311))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X307)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9336,f390])).

fof(f9336,plain,(
    ! [X30,X28,X26,X29,X27] :
      ( r2_hidden(sK9(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X27,k2_zfmisc_1(X28,sK9(k1_zfmisc_1(X26)))))),X29),X30)),X26)
      | v1_xboole_0(sK9(k1_zfmisc_1(X26)))
      | v1_xboole_0(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X27,k2_zfmisc_1(X28,sK9(k1_zfmisc_1(X26)))))),X29),X30)) ) ),
    inference(resolution,[],[f9331,f388])).

fof(f17416,plain,
    ( spl13_56
    | spl13_118
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f17412,f162,f17414,f393])).

fof(f17414,plain,
    ( spl13_118
  <=> ! [X1,X3,X5,X0,X2,X4,X6] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k9_relat_1(sK2,X3)))))),X4),X5),X6))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k9_relat_1(sK2,X3)))))),X4),X5),X6)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_118])])).

fof(f17412,plain,
    ( ! [X6,X4,X2,X0,X5,X3,X1] :
        ( v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k9_relat_1(sK2,X3)))))),X4),X5),X6))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k2_zfmisc_1(X1,k2_zfmisc_1(X2,k9_relat_1(sK2,X3)))))),X4),X5),X6)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f17349,f119])).

fof(f17349,plain,
    ( ! [X366,X368,X370,X365,X367,X369,X371] :
        ( m1_subset_1(sK9(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X365,k2_zfmisc_1(X366,k2_zfmisc_1(X367,k9_relat_1(sK2,X368)))))),X369),X370),X371)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(k9_relat_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X365,k2_zfmisc_1(X366,k2_zfmisc_1(X367,k9_relat_1(sK2,X368)))))),X369),X370),X371)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f10124,f390])).

fof(f14242,plain,
    ( spl13_56
    | spl13_116
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f14238,f162,f14240,f393])).

fof(f14240,plain,
    ( spl13_116
  <=> ! [X0] :
        ( v1_xboole_0(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | v1_xboole_0(k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_116])])).

fof(f14238,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f10408,f119])).

fof(f10408,plain,
    ( ! [X154] :
        ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X154)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X154))))))))
        | v1_xboole_0(k9_relat_1(sK2,X154))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X154)))))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X154))))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f5613,f390])).

fof(f5613,plain,(
    ! [X199] :
      ( r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X199))))))),X199)
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X199))))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X199)))))))
      | v1_xboole_0(X199)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X199)))) ) ),
    inference(resolution,[],[f1673,f119])).

fof(f1673,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))))),X0)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))))) ) ),
    inference(resolution,[],[f619,f277])).

fof(f619,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X0)))))))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X0))))
      | m1_subset_1(X1,X0)
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k1_zfmisc_1(X0)))))) ) ),
    inference(resolution,[],[f370,f126])).

fof(f13868,plain,
    ( spl13_56
    | spl13_114
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f13862,f162,f13866,f393])).

fof(f13866,plain,
    ( spl13_114
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(k7_relset_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))),X2,X3))
        | r2_hidden(sK9(k7_relset_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))),X2,X3)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | v1_xboole_0(k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_114])])).

fof(f13862,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(k7_relset_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))),X2,X3))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k7_relset_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))),X2,X3)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9173,f119])).

fof(f9173,plain,
    ( ! [X212,X210,X213,X211] :
        ( m1_subset_1(sK9(k7_relset_1(X211,sK9(k1_zfmisc_1(k9_relat_1(sK2,X212))),X210,X213)),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X211,sK9(k1_zfmisc_1(k9_relat_1(sK2,X212))),X210,X213))
        | v1_xboole_0(k9_relat_1(sK2,X212))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X212))))
        | ~ m1_subset_1(X210,k1_zfmisc_1(k2_zfmisc_1(X211,sK9(k1_zfmisc_1(k9_relat_1(sK2,X212)))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f4559,f390])).

fof(f13859,plain,
    ( spl13_56
    | spl13_112
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f13853,f162,f13857,f393])).

fof(f13857,plain,
    ( spl13_112
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X0,k9_relat_1(sK2,X1),X2,X3))))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k7_relset_1(X0,k9_relat_1(sK2,X1),X2,X3)))),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X0,k9_relat_1(sK2,X1),X2,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k9_relat_1(sK2,X1))))
        | v1_xboole_0(k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_112])])).

fof(f13853,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X0,k9_relat_1(sK2,X1),X2,X3))))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k9_relat_1(sK2,X1))))
        | v1_xboole_0(k7_relset_1(X0,k9_relat_1(sK2,X1),X2,X3))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k7_relset_1(X0,k9_relat_1(sK2,X1),X2,X3)))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9111,f119])).

fof(f9111,plain,
    ( ! [X212,X210,X213,X211] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k7_relset_1(X210,k9_relat_1(sK2,X211),X212,X213)))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X210,k9_relat_1(sK2,X211),X212,X213))))
        | v1_xboole_0(k9_relat_1(sK2,X211))
        | ~ m1_subset_1(X212,k1_zfmisc_1(k2_zfmisc_1(X210,k9_relat_1(sK2,X211))))
        | v1_xboole_0(k7_relset_1(X210,k9_relat_1(sK2,X211),X212,X213)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f4281,f390])).

fof(f4281,plain,(
    ! [X335,X337,X336,X338] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(k7_relset_1(X336,X337,X335,X338)))),X337)
      | v1_xboole_0(k7_relset_1(X336,X337,X335,X338))
      | v1_xboole_0(sK9(k1_zfmisc_1(k7_relset_1(X336,X337,X335,X338))))
      | v1_xboole_0(X337)
      | ~ m1_subset_1(X335,k1_zfmisc_1(k2_zfmisc_1(X336,X337))) ) ),
    inference(resolution,[],[f536,f119])).

fof(f13849,plain,
    ( spl13_56
    | spl13_110
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f13845,f162,f13847,f393])).

fof(f13847,plain,
    ( spl13_110
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X0))))),X2))),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X0))))),X2))
        | v1_xboole_0(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X0))))),X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_110])])).

fof(f13845,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X0))))),X2)))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X0))))),X2))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k1_zfmisc_1(k9_relat_1(sK2,X0))))),X2))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f8723,f119])).

fof(f8723,plain,
    ( ! [X163,X164,X162] :
        ( m1_subset_1(sK9(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X162,k1_zfmisc_1(k9_relat_1(sK2,X163))))),X164))),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X163))
        | v1_xboole_0(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X162,k1_zfmisc_1(k9_relat_1(sK2,X163))))),X164)))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X162,k1_zfmisc_1(k9_relat_1(sK2,X163))))),X164)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f8658,f267])).

fof(f8658,plain,
    ( ! [X222,X223,X221,X224] :
        ( ~ r1_tarski(X221,k2_zfmisc_1(X222,k1_zfmisc_1(k9_relat_1(sK2,X223))))
        | v1_xboole_0(k9_relat_1(X221,X224))
        | v1_xboole_0(k9_relat_1(sK2,X223))
        | v1_xboole_0(sK9(k9_relat_1(X221,X224)))
        | m1_subset_1(sK9(sK9(k9_relat_1(X221,X224))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f8602,f390])).

fof(f8602,plain,(
    ! [X472,X474,X471,X473] :
      ( r2_hidden(sK9(sK9(k9_relat_1(X471,X472))),X474)
      | ~ r1_tarski(X471,k2_zfmisc_1(X473,k1_zfmisc_1(X474)))
      | v1_xboole_0(k9_relat_1(X471,X472))
      | v1_xboole_0(X474)
      | v1_xboole_0(sK9(k9_relat_1(X471,X472))) ) ),
    inference(resolution,[],[f8535,f119])).

fof(f8535,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(sK9(k9_relat_1(X0,X1))),X2)
      | v1_xboole_0(sK9(k9_relat_1(X0,X1)))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,k1_zfmisc_1(X2)))
      | v1_xboole_0(k9_relat_1(X0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f8478])).

fof(f8478,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(sK9(k9_relat_1(X0,X1)))
      | m1_subset_1(sK9(sK9(k9_relat_1(X0,X1))),X2)
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,k1_zfmisc_1(X2)))
      | v1_xboole_0(k9_relat_1(X0,X1))
      | ~ r1_tarski(X0,k2_zfmisc_1(X3,k1_zfmisc_1(X2))) ) ),
    inference(resolution,[],[f8477,f123])).

fof(f8477,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1))))
      | v1_xboole_0(sK9(k9_relat_1(X2,X3)))
      | m1_subset_1(sK9(sK9(k9_relat_1(X2,X3))),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,k1_zfmisc_1(X1)))
      | v1_xboole_0(k9_relat_1(X2,X3)) ) ),
    inference(superposition,[],[f8420,f129])).

fof(f8420,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3))
      | v1_xboole_0(sK9(k9_relat_1(X2,X3)))
      | m1_subset_1(sK9(sK9(k9_relat_1(X2,X3))),X1)
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f8419,f123])).

fof(f8419,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1))))
      | v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3))
      | v1_xboole_0(sK9(k9_relat_1(X2,X3)))
      | m1_subset_1(sK9(sK9(k9_relat_1(X2,X3))),X1) ) ),
    inference(duplicate_literal_removal,[],[f8418])).

fof(f8418,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(sK9(k9_relat_1(X2,X3)))
      | v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1))))
      | m1_subset_1(sK9(sK9(k9_relat_1(X2,X3))),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1)))) ) ),
    inference(superposition,[],[f8417,f129])).

fof(f8417,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(sK9(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3)))
      | v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1))))
      | m1_subset_1(sK9(sK9(k9_relat_1(X2,X3))),X1) ) ),
    inference(duplicate_literal_removal,[],[f8416])).

fof(f8416,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK9(sK9(k9_relat_1(X2,X3))),X1)
      | v1_xboole_0(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1))))
      | v1_xboole_0(sK9(k7_relset_1(X0,k1_zfmisc_1(X1),X2,X3)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_zfmisc_1(X1)))) ) ),
    inference(superposition,[],[f2368,f129])).

fof(f13841,plain,
    ( spl13_56
    | spl13_108
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f13837,f162,f13839,f393])).

fof(f13839,plain,
    ( spl13_108
  <=> ! [X0] :
        ( v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_108])])).

fof(f13837,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f7143,f119])).

fof(f7143,plain,
    ( ! [X134] :
        ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X134)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X134))))))))
        | v1_xboole_0(k9_relat_1(sK2,X134))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X134))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X134))))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f3888,f390])).

fof(f3888,plain,(
    ! [X187] :
      ( r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(X187))))))),X187)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(X187))))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(X187)))))))
      | v1_xboole_0(X187)
      | v1_xboole_0(sK9(k1_zfmisc_1(X187))) ) ),
    inference(resolution,[],[f990,f119])).

fof(f990,plain,(
    ! [X54] :
      ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(X54))))))),X54)
      | v1_xboole_0(sK9(k1_zfmisc_1(X54)))
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(X54))))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(sK9(k1_zfmisc_1(X54))))))) ) ),
    inference(resolution,[],[f722,f323])).

fof(f722,plain,(
    ! [X33] :
      ( r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X33))))),X33)
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X33)))))
      | v1_xboole_0(X33)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X33)))) ) ),
    inference(resolution,[],[f510,f119])).

fof(f13833,plain,
    ( spl13_56
    | spl13_106
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f13829,f162,f13831,f393])).

fof(f13831,plain,
    ( spl13_106
  <=> ! [X0] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | v1_xboole_0(k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_106])])).

fof(f13829,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f6796,f119])).

fof(f6796,plain,
    ( ! [X121] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X121)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X121))))))))
        | v1_xboole_0(k9_relat_1(sK2,X121))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X121)))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X121)))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f3616,f390])).

fof(f3616,plain,(
    ! [X187] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X187))))))),X187)
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X187)))))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X187)))))))
      | v1_xboole_0(X187)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X187)))) ) ),
    inference(resolution,[],[f511,f119])).

fof(f511,plain,(
    ! [X1] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X1))))))),X1)
      | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(X1))))
      | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X1)))))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(X1))))))) ) ),
    inference(resolution,[],[f359,f362])).

fof(f11040,plain,
    ( spl13_56
    | spl13_104
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f11036,f162,f11038,f393])).

fof(f11038,plain,
    ( spl13_104
  <=> ! [X0] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(k9_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_104])])).

fof(f11036,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f5665,f119])).

fof(f5665,plain,
    ( ! [X121] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X121)))))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X121))))))
        | v1_xboole_0(k9_relat_1(sK2,X121))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X121))))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X121)))))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f3233,f390])).

fof(f3233,plain,(
    ! [X173] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X173))))))),X173)
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X173)))))))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X173)))))
      | v1_xboole_0(X173)
      | v1_xboole_0(sK9(k1_zfmisc_1(X173))) ) ),
    inference(resolution,[],[f829,f119])).

fof(f829,plain,(
    ! [X45] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X45))))))),X45)
      | v1_xboole_0(sK9(k1_zfmisc_1(X45)))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X45)))))))
      | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(X45))))) ) ),
    inference(resolution,[],[f629,f323])).

fof(f11035,plain,
    ( spl13_56
    | spl13_102
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f11031,f162,f11033,f393])).

fof(f11033,plain,
    ( spl13_102
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))),X2)))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))),X2))))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_102])])).

fof(f11031,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))),X2))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))),X2))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))),X2)))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9941,f119])).

fof(f9941,plain,
    ( ! [X204,X202,X203] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X202,k9_relat_1(sK2,X203)))),X204)))),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X203))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X202,k9_relat_1(sK2,X203)))),X204))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X202,k9_relat_1(sK2,X203)))),X204)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f4653,f390])).

fof(f4653,plain,(
    ! [X292,X294,X293] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X292,X293))),X294)))),X293)
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X292,X293))),X294))))
      | v1_xboole_0(X293)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X292,X293))),X294)) ) ),
    inference(resolution,[],[f460,f119])).

fof(f460,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X5)))),X4)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X5))
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X3,X4))),X5)))) ) ),
    inference(resolution,[],[f404,f362])).

fof(f9434,plain,
    ( spl13_56
    | spl13_100
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f9430,f162,f9432,f393])).

fof(f9432,plain,
    ( spl13_100
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))),X2))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_100])])).

fof(f9430,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))),X2))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9389,f119])).

fof(f9389,plain,
    ( ! [X189,X187,X188] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X188,sK9(k1_zfmisc_1(k9_relat_1(sK2,X187)))))),X189)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X188,sK9(k1_zfmisc_1(k9_relat_1(sK2,X187)))))),X189))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X187)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f9352,f390])).

fof(f8036,plain,
    ( spl13_56
    | spl13_98
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f8030,f162,f8034,f393])).

fof(f8034,plain,
    ( spl13_98
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(k9_relat_1(k7_relset_1(X5,k2_zfmisc_1(X1,k9_relat_1(sK2,X0)),X2,X3),X4)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))))
        | v1_xboole_0(k7_relset_1(X1,k9_relat_1(sK2,X0),k9_relat_1(X2,X3),X4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_98])])).

fof(f8030,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(k7_relset_1(X1,k9_relat_1(sK2,X0),k9_relat_1(X2,X3),X4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X5,k2_zfmisc_1(X1,k9_relat_1(sK2,X0)))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(k7_relset_1(X5,k2_zfmisc_1(X1,k9_relat_1(sK2,X0)),X2,X3),X4)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f7888,f119])).

fof(f7888,plain,
    ( ! [X261,X257,X259,X260,X256,X258] :
        ( m1_subset_1(sK9(k9_relat_1(k7_relset_1(X257,k2_zfmisc_1(X258,k9_relat_1(sK2,X259)),X256,X260),X261)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X259))
        | v1_xboole_0(k7_relset_1(X258,k9_relat_1(sK2,X259),k9_relat_1(X256,X260),X261))
        | ~ m1_subset_1(X256,k1_zfmisc_1(k2_zfmisc_1(X257,k2_zfmisc_1(X258,k9_relat_1(sK2,X259))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f7806,f390])).

fof(f4445,plain,
    ( spl13_56
    | spl13_96
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f4441,f162,f4443,f393])).

fof(f4443,plain,
    ( spl13_96
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X0,X1))))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X1)))),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X3,k9_relat_1(sK2,X2),X0,X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k9_relat_1(sK2,X2))))
        | v1_xboole_0(k9_relat_1(sK2,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_96])])).

fof(f4441,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X0,X1))))
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,k9_relat_1(sK2,X2))))
        | v1_xboole_0(k7_relset_1(X3,k9_relat_1(sK2,X2),X0,X1))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(X0,X1)))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f4411,f119])).

fof(f4411,plain,
    ( ! [X191,X192,X190,X193] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(X192,X193)))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X192,X193))))
        | v1_xboole_0(k9_relat_1(sK2,X191))
        | ~ m1_subset_1(X192,k1_zfmisc_1(k2_zfmisc_1(X190,k9_relat_1(sK2,X191))))
        | v1_xboole_0(k7_relset_1(X190,k9_relat_1(sK2,X191),X192,X193)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f4336,f390])).

fof(f4336,plain,(
    ! [X346,X345,X347,X348] :
      ( r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(X345,X348)))),X347)
      | v1_xboole_0(k7_relset_1(X346,X347,X345,X348))
      | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(X345,X348))))
      | v1_xboole_0(X347)
      | ~ m1_subset_1(X345,k1_zfmisc_1(k2_zfmisc_1(X346,X347))) ) ),
    inference(resolution,[],[f4285,f119])).

fof(f4060,plain,
    ( spl13_56
    | spl13_94
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f4056,f162,f4058,f393])).

fof(f4058,plain,
    ( spl13_94
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_94])])).

fof(f4056,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),X2))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X1,sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f3388,f119])).

fof(f3388,plain,
    ( ! [X152,X151,X153] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X152,sK9(k1_zfmisc_1(k9_relat_1(sK2,X151)))))),X153)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X151))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X152,sK9(k1_zfmisc_1(k9_relat_1(sK2,X151)))))),X153))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X151)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f2608,f390])).

fof(f2608,plain,(
    ! [X212,X213,X214] :
      ( r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X212,sK9(k1_zfmisc_1(X213))))),X214)),X213)
      | v1_xboole_0(sK9(k1_zfmisc_1(X213)))
      | v1_xboole_0(X213)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X212,sK9(k1_zfmisc_1(X213))))),X214)) ) ),
    inference(resolution,[],[f895,f119])).

fof(f895,plain,(
    ! [X72,X71,X73] :
      ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X72,sK9(k1_zfmisc_1(X71))))),X73)),X71)
      | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X72,sK9(k1_zfmisc_1(X71))))),X73))
      | v1_xboole_0(sK9(k1_zfmisc_1(X71))) ) ),
    inference(resolution,[],[f661,f323])).

fof(f2890,plain,
    ( spl13_56
    | spl13_92
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f2884,f162,f2888,f393])).

fof(f2888,plain,
    ( spl13_92
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_2(X0,X1,k9_relat_1(sK2,X2))
        | r2_hidden(k3_funct_2(X1,k9_relat_1(sK2,X2),X0,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))
        | ~ m1_subset_1(X3,X1)
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | v1_xboole_0(X1)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_92])])).

fof(f2884,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_2(X0,X1,k9_relat_1(sK2,X2))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(k9_relat_1(sK2,X2))
        | ~ m1_subset_1(X3,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k9_relat_1(sK2,X2))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(k3_funct_2(X1,k9_relat_1(sK2,X2),X0,X3),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f2199,f119])).

fof(f2199,plain,
    ( ! [X107,X105,X106,X104] :
        ( m1_subset_1(k3_funct_2(X105,k9_relat_1(sK2,X106),X104,X107),u1_struct_0(sK0))
        | ~ v1_funct_2(X104,X105,k9_relat_1(sK2,X106))
        | ~ v1_funct_1(X104)
        | v1_xboole_0(X105)
        | v1_xboole_0(k9_relat_1(sK2,X106))
        | ~ m1_subset_1(X107,X105)
        | ~ m1_subset_1(X104,k1_zfmisc_1(k2_zfmisc_1(X105,k9_relat_1(sK2,X106)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f696,f390])).

fof(f1730,plain,
    ( spl13_56
    | spl13_90
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1724,f162,f1728,f393])).

fof(f1728,plain,
    ( spl13_90
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(k7_relset_1(X2,k9_relat_1(sK2,X0),X1,X3)),u1_struct_0(sK0))
        | v1_xboole_0(k7_relset_1(X2,k9_relat_1(sK2,X0),X1,X3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_90])])).

fof(f1724,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k9_relat_1(sK2,X0))))
        | v1_xboole_0(k7_relset_1(X2,k9_relat_1(sK2,X0),X1,X3))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k7_relset_1(X2,k9_relat_1(sK2,X0),X1,X3)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f1296,f119])).

fof(f1296,plain,
    ( ! [X74,X72,X71,X73] :
        ( m1_subset_1(sK9(k7_relset_1(X71,k9_relat_1(sK2,X72),X73,X74)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X72))
        | ~ m1_subset_1(X73,k1_zfmisc_1(k2_zfmisc_1(X71,k9_relat_1(sK2,X72))))
        | v1_xboole_0(k7_relset_1(X71,k9_relat_1(sK2,X72),X73,X74)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f779,f390])).

fof(f1637,plain,
    ( spl13_56
    | spl13_88
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1633,f162,f1635,f393])).

fof(f1635,plain,
    ( spl13_88
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_88])])).

fof(f1633,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f985,f119])).

fof(f985,plain,
    ( ! [X41] :
        ( m1_subset_1(sK9(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X41)))))),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X41))
        | v1_xboole_0(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X41)))))
        | v1_xboole_0(sK9(sK9(k1_zfmisc_1(k1_zfmisc_1(k9_relat_1(sK2,X41)))))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f722,f390])).

fof(f1629,plain,
    ( spl13_56
    | spl13_86
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1625,f162,f1627,f393])).

fof(f1627,plain,
    ( spl13_86
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_86])])).

fof(f1625,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f821,f119])).

fof(f821,plain,
    ( ! [X11] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X11)))))),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X11))
        | v1_xboole_0(sK9(k1_zfmisc_1(sK9(k1_zfmisc_1(k9_relat_1(sK2,X11))))))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X11)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f629,f390])).

fof(f1332,plain,
    ( spl13_56
    | spl13_84
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1321,f162,f1330,f393])).

fof(f1330,plain,
    ( spl13_84
  <=> ! [X82] :
        ( v1_xboole_0(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X82))
        | r2_hidden(sK9(k9_relat_1(sK2,X82)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_84])])).

fof(f1321,plain,
    ( ! [X82] :
        ( v1_xboole_0(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X82))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK2,X82)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f1308,f163])).

fof(f1308,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(X1)
      | r2_hidden(sK9(k9_relat_1(X2,X3)),X1) ) ),
    inference(duplicate_literal_removal,[],[f1307])).

fof(f1307,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK9(k9_relat_1(X2,X3)),X1)
      | v1_xboole_0(k7_relset_1(X0,X1,X2,X3))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f779,f129])).

fof(f1285,plain,
    ( ~ spl13_83
    | ~ spl13_78 ),
    inference(avatar_split_clause,[],[f1277,f1264,f1283])).

fof(f1283,plain,
    ( spl13_83
  <=> ~ r2_hidden(u1_struct_0(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_83])])).

fof(f1277,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),sK3)
    | ~ spl13_78 ),
    inference(resolution,[],[f1265,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',antisymmetry_r2_hidden)).

fof(f1274,plain,
    ( spl13_80
    | spl13_70
    | ~ spl13_76 ),
    inference(avatar_split_clause,[],[f1267,f1256,f1177,f1272])).

fof(f1272,plain,
    ( spl13_80
  <=> r2_hidden(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_80])])).

fof(f1267,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_76 ),
    inference(resolution,[],[f1257,f119])).

fof(f1257,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | ~ spl13_76 ),
    inference(avatar_component_clause,[],[f1256])).

fof(f1266,plain,
    ( spl13_78
    | spl13_70
    | ~ spl13_4 ),
    inference(avatar_split_clause,[],[f1259,f151,f1177,f1264])).

fof(f1259,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl13_4 ),
    inference(resolution,[],[f152,f119])).

fof(f152,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1258,plain,
    ( spl13_18
    | ~ spl13_17
    | ~ spl13_15
    | spl13_24
    | ~ spl13_23
    | ~ spl13_21
    | ~ spl13_13
    | ~ spl13_11
    | spl13_0
    | spl13_76
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1244,f162,f1256,f135,f166,f173,f201,f208,f215,f180,f187,f194])).

fof(f1244,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl13_8 ),
    inference(resolution,[],[f109,f163])).

fof(f1191,plain,
    ( spl13_56
    | spl13_74
    | ~ spl13_72 ),
    inference(avatar_split_clause,[],[f1187,f1180,f1189,f393])).

fof(f1189,plain,
    ( spl13_74
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k1_funct_1(sK2,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_74])])).

fof(f1180,plain,
    ( spl13_72
  <=> ! [X82] :
        ( ~ m1_subset_1(X82,u1_struct_0(sK1))
        | m1_subset_1(k1_funct_1(sK2,X82),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_72])])).

fof(f1187,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(k1_funct_1(sK2,X0),u1_struct_0(sK0)) )
    | ~ spl13_72 ),
    inference(resolution,[],[f1181,f119])).

fof(f1181,plain,
    ( ! [X82] :
        ( m1_subset_1(k1_funct_1(sK2,X82),u1_struct_0(sK0))
        | ~ m1_subset_1(X82,u1_struct_0(sK1)) )
    | ~ spl13_72 ),
    inference(avatar_component_clause,[],[f1180])).

fof(f1186,plain,
    ( spl13_18
    | ~ spl13_33
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1184,f1177,f246,f194])).

fof(f246,plain,
    ( spl13_33
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_33])])).

fof(f1184,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl13_70 ),
    inference(resolution,[],[f1178,f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',fc2_struct_0)).

fof(f1178,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl13_70 ),
    inference(avatar_component_clause,[],[f1177])).

fof(f1185,plain,
    ( ~ spl13_15
    | spl13_18
    | ~ spl13_70 ),
    inference(avatar_split_clause,[],[f1183,f1177,f194,f180])).

fof(f1183,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl13_70 ),
    inference(resolution,[],[f1178,f526])).

fof(f526,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(u1_struct_0(X5))
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X5) ) ),
    inference(global_subsumption,[],[f104,f106])).

fof(f104,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',dt_l1_pre_topc)).

fof(f1182,plain,
    ( spl13_70
    | ~ spl13_13
    | ~ spl13_11
    | spl13_72
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1165,f162,f1180,f166,f173,f1177])).

fof(f1165,plain,
    ( ! [X82] :
        ( ~ m1_subset_1(X82,u1_struct_0(sK1))
        | m1_subset_1(k1_funct_1(sK2,X82),u1_struct_0(sK0))
        | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(sK2)
        | v1_xboole_0(u1_struct_0(sK1)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f933,f163])).

fof(f933,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k1_funct_1(X2,X3),X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f932])).

fof(f932,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_funct_1(X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f130,f131])).

fof(f1149,plain,
    ( spl13_56
    | spl13_68
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f1145,f162,f1147,f393])).

fof(f1147,plain,
    ( spl13_68
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k9_relat_1(sK2,X1)))),X2))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k9_relat_1(sK2,X1)))),X2)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_68])])).

fof(f1145,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k9_relat_1(sK2,X1)))),X2))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X0,k9_relat_1(sK2,X1)))),X2)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f887,f119])).

fof(f887,plain,
    ( ! [X23,X21,X22] :
        ( m1_subset_1(sK9(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X22,k9_relat_1(sK2,X21)))),X23)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK9(k1_zfmisc_1(k2_zfmisc_1(X22,k9_relat_1(sK2,X21)))),X23))
        | v1_xboole_0(k9_relat_1(sK2,X21)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f661,f390])).

fof(f531,plain,
    ( spl13_56
    | spl13_66
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f527,f162,f529,f393])).

fof(f529,plain,
    ( spl13_66
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))),u1_struct_0(sK0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_66])])).

fof(f527,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0))))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK2,X0)))),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f403,f119])).

fof(f403,plain,
    ( ! [X1] :
        ( m1_subset_1(sK9(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X1))
        | v1_xboole_0(sK9(k1_zfmisc_1(k9_relat_1(sK2,X1)))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f390,f362])).

fof(f441,plain,
    ( spl13_62
    | spl13_64
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f431,f162,f439,f433])).

fof(f433,plain,
    ( spl13_62
  <=> ! [X5] : r2_hidden(k9_relat_1(sK2,X5),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_62])])).

fof(f439,plain,
    ( spl13_64
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f431,plain,
    ( ! [X5] :
        ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(k9_relat_1(sK2,X5),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f425,f119])).

fof(f425,plain,
    ( ! [X10] : m1_subset_1(k9_relat_1(sK2,X10),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl13_8 ),
    inference(resolution,[],[f383,f163])).

fof(f412,plain,
    ( spl13_24
    | ~ spl13_35
    | ~ spl13_56 ),
    inference(avatar_split_clause,[],[f411,f393,f253,f215])).

fof(f253,plain,
    ( spl13_35
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_35])])).

fof(f411,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl13_56 ),
    inference(resolution,[],[f394,f106])).

fof(f394,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl13_56 ),
    inference(avatar_component_clause,[],[f393])).

fof(f410,plain,
    ( spl13_56
    | spl13_60
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f406,f162,f408,f393])).

fof(f408,plain,
    ( spl13_60
  <=> ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | r2_hidden(sK9(k9_relat_1(sK2,X0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_60])])).

fof(f406,plain,
    ( ! [X0] :
        ( v1_xboole_0(k9_relat_1(sK2,X0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(sK9(k9_relat_1(sK2,X0)),u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f402,f119])).

fof(f402,plain,
    ( ! [X0] :
        ( m1_subset_1(sK9(k9_relat_1(sK2,X0)),u1_struct_0(sK0))
        | v1_xboole_0(k9_relat_1(sK2,X0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f390,f277])).

fof(f401,plain,
    ( ~ spl13_57
    | spl13_58
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f391,f162,f399,f396])).

fof(f396,plain,
    ( spl13_57
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_57])])).

fof(f399,plain,
    ( spl13_58
  <=> ! [X3,X2] : ~ r2_hidden(X2,k9_relat_1(sK2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_58])])).

fof(f391,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k9_relat_1(sK2,X3))
        | ~ v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl13_8 ),
    inference(resolution,[],[f387,f309])).

fof(f309,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_tarski(X5,X3)
      | ~ r2_hidden(X4,X5)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f127,f123])).

fof(f352,plain,
    ( ~ spl13_55
    | ~ spl13_50 ),
    inference(avatar_split_clause,[],[f345,f329,f350])).

fof(f350,plain,
    ( spl13_55
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_55])])).

fof(f329,plain,
    ( spl13_50
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_50])])).

fof(f345,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ spl13_50 ),
    inference(duplicate_literal_removal,[],[f344])).

fof(f344,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),sK2)
    | ~ spl13_50 ),
    inference(resolution,[],[f342,f330])).

fof(f330,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl13_50 ),
    inference(avatar_component_clause,[],[f329])).

fof(f342,plain,
    ( ! [X1] :
        ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),X1)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl13_50 ),
    inference(resolution,[],[f330,f117])).

fof(f340,plain,
    ( spl13_52
    | ~ spl13_46 ),
    inference(avatar_split_clause,[],[f333,f311,f338])).

fof(f338,plain,
    ( spl13_52
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_52])])).

fof(f311,plain,
    ( spl13_46
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_46])])).

fof(f333,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_46 ),
    inference(resolution,[],[f312,f277])).

fof(f312,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl13_46 ),
    inference(avatar_component_clause,[],[f311])).

fof(f332,plain,
    ( ~ spl13_49
    | spl13_46
    | ~ spl13_38 ),
    inference(avatar_split_clause,[],[f322,f273,f311,f317])).

fof(f317,plain,
    ( spl13_49
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_49])])).

fof(f322,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) )
    | ~ spl13_38 ),
    inference(resolution,[],[f309,f274])).

fof(f331,plain,
    ( spl13_48
    | spl13_50
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f327,f162,f329,f314])).

fof(f314,plain,
    ( spl13_48
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f327,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | r2_hidden(X0,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) )
    | ~ spl13_8 ),
    inference(resolution,[],[f324,f119])).

fof(f324,plain,
    ( ! [X2] :
        ( m1_subset_1(X2,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl13_8 ),
    inference(resolution,[],[f126,f163])).

fof(f319,plain,
    ( spl13_46
    | ~ spl13_49
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f308,f162,f317,f311])).

fof(f308,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK2) )
    | ~ spl13_8 ),
    inference(resolution,[],[f127,f163])).

fof(f306,plain,
    ( ~ spl13_43
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f298,f284,f287])).

fof(f287,plain,
    ( spl13_43
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_43])])).

fof(f284,plain,
    ( spl13_40
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_40])])).

fof(f298,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_40 ),
    inference(resolution,[],[f285,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t7_boole)).

fof(f285,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_40 ),
    inference(avatar_component_clause,[],[f284])).

fof(f305,plain,
    ( ~ spl13_45
    | ~ spl13_40 ),
    inference(avatar_split_clause,[],[f297,f284,f303])).

fof(f303,plain,
    ( spl13_45
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_45])])).

fof(f297,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))),sK2)
    | ~ spl13_40 ),
    inference(resolution,[],[f285,f117])).

fof(f292,plain,
    ( spl13_40
    | spl13_42
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f278,f162,f290,f284])).

fof(f290,plain,
    ( spl13_42
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_42])])).

fof(f278,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl13_8 ),
    inference(resolution,[],[f119,f163])).

fof(f275,plain,
    ( spl13_38
    | ~ spl13_8 ),
    inference(avatar_split_clause,[],[f268,f162,f273])).

fof(f268,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl13_8 ),
    inference(resolution,[],[f122,f163])).

fof(f265,plain,
    ( spl13_36
    | ~ spl13_30 ),
    inference(avatar_split_clause,[],[f244,f239,f263])).

fof(f263,plain,
    ( spl13_36
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_36])])).

fof(f239,plain,
    ( spl13_30
  <=> l1_pre_topc(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_30])])).

fof(f244,plain,
    ( l1_struct_0(sK12)
    | ~ spl13_30 ),
    inference(resolution,[],[f104,f240])).

fof(f240,plain,
    ( l1_pre_topc(sK12)
    | ~ spl13_30 ),
    inference(avatar_component_clause,[],[f239])).

fof(f258,plain,
    ( spl13_34
    | ~ spl13_20 ),
    inference(avatar_split_clause,[],[f243,f204,f256])).

fof(f256,plain,
    ( spl13_34
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_34])])).

fof(f204,plain,
    ( spl13_20
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_20])])).

fof(f243,plain,
    ( l1_struct_0(sK0)
    | ~ spl13_20 ),
    inference(resolution,[],[f104,f205])).

fof(f205,plain,
    ( l1_pre_topc(sK0)
    | ~ spl13_20 ),
    inference(avatar_component_clause,[],[f204])).

fof(f251,plain,
    ( spl13_32
    | ~ spl13_14 ),
    inference(avatar_split_clause,[],[f242,f183,f249])).

fof(f249,plain,
    ( spl13_32
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_32])])).

fof(f183,plain,
    ( spl13_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_14])])).

fof(f242,plain,
    ( l1_struct_0(sK1)
    | ~ spl13_14 ),
    inference(resolution,[],[f104,f184])).

fof(f184,plain,
    ( l1_pre_topc(sK1)
    | ~ spl13_14 ),
    inference(avatar_component_clause,[],[f183])).

fof(f241,plain,(
    spl13_30 ),
    inference(avatar_split_clause,[],[f133,f239])).

fof(f133,plain,(
    l1_pre_topc(sK12) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    l1_pre_topc(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f19,f89])).

fof(f89,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK12) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',existence_l1_pre_topc)).

fof(f234,plain,(
    spl13_28 ),
    inference(avatar_split_clause,[],[f132,f232])).

fof(f232,plain,
    ( spl13_28
  <=> l1_struct_0(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_28])])).

fof(f132,plain,(
    l1_struct_0(sK11) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    l1_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f20,f87])).

fof(f87,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK11) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',existence_l1_struct_0)).

fof(f227,plain,(
    spl13_26 ),
    inference(avatar_split_clause,[],[f103,f225])).

fof(f225,plain,
    ( spl13_26
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_26])])).

fof(f103,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f220,plain,(
    ~ spl13_25 ),
    inference(avatar_split_clause,[],[f91,f218])).

fof(f218,plain,
    ( spl13_25
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_25])])).

fof(f91,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
    ( ( ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
        & m1_subset_1(sK3,u1_struct_0(sK1)) )
      | ~ v5_pre_topc(sK2,sK1,sK0) )
    & ( ! [X4] :
          ( r1_tmap_1(sK1,sK0,sK2,X4)
          | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
      | v5_pre_topc(sK2,sK1,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f69,f68,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | v5_pre_topc(X2,X1,X0) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,sK0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,sK0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,sK0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,sK0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(sK0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ r1_tmap_1(sK1,X0,X2,X3)
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              | ~ v5_pre_topc(X2,sK1,X0) )
            & ( ! [X4] :
                  ( r1_tmap_1(sK1,X0,X2,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(sK1)) )
              | v5_pre_topc(X2,sK1,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X0))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ r1_tmap_1(X1,X0,X2,X3)
                & m1_subset_1(X3,u1_struct_0(X1)) )
            | ~ v5_pre_topc(X2,X1,X0) )
          & ( ! [X4] :
                ( r1_tmap_1(X1,X0,X2,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | v5_pre_topc(X2,X1,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ r1_tmap_1(X1,X0,sK2,X3)
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ v5_pre_topc(sK2,X1,X0) )
        & ( ! [X4] :
              ( r1_tmap_1(X1,X0,sK2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          | v5_pre_topc(sK2,X1,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK3)
        & m1_subset_1(sK3,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X4] :
                    ( r1_tmap_1(X1,X0,X2,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ r1_tmap_1(X1,X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ v5_pre_topc(X2,X1,X0) )
              & ( ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | v5_pre_topc(X2,X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( v5_pre_topc(X2,X1,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t49_tmap_1.p',t49_tmap_1)).

fof(f213,plain,(
    spl13_22 ),
    inference(avatar_split_clause,[],[f92,f211])).

fof(f211,plain,
    ( spl13_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_22])])).

fof(f92,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f206,plain,(
    spl13_20 ),
    inference(avatar_split_clause,[],[f93,f204])).

fof(f93,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f199,plain,(
    ~ spl13_19 ),
    inference(avatar_split_clause,[],[f94,f197])).

fof(f197,plain,
    ( spl13_19
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_19])])).

fof(f94,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f192,plain,(
    spl13_16 ),
    inference(avatar_split_clause,[],[f95,f190])).

fof(f190,plain,
    ( spl13_16
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f95,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f185,plain,(
    spl13_14 ),
    inference(avatar_split_clause,[],[f96,f183])).

fof(f96,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f178,plain,(
    spl13_12 ),
    inference(avatar_split_clause,[],[f97,f176])).

fof(f176,plain,
    ( spl13_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_12])])).

fof(f97,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f171,plain,(
    spl13_10 ),
    inference(avatar_split_clause,[],[f98,f169])).

fof(f169,plain,
    ( spl13_10
  <=> v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f98,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f70])).

fof(f164,plain,(
    spl13_8 ),
    inference(avatar_split_clause,[],[f99,f162])).

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f70])).

fof(f157,plain,
    ( spl13_0
    | spl13_6 ),
    inference(avatar_split_clause,[],[f100,f155,f135])).

fof(f100,plain,(
    ! [X4] :
      ( r1_tmap_1(sK1,sK0,sK2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK1))
      | v5_pre_topc(sK2,sK1,sK0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f153,plain,
    ( ~ spl13_1
    | spl13_4 ),
    inference(avatar_split_clause,[],[f101,f151,f138])).

fof(f101,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f146,plain,
    ( ~ spl13_1
    | ~ spl13_3 ),
    inference(avatar_split_clause,[],[f102,f144,f138])).

fof(f102,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).
%------------------------------------------------------------------------------
