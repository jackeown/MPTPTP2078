%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1817+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:39 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  220 (1714 expanded)
%              Number of leaves         :   42 ( 800 expanded)
%              Depth                    :   11
%              Number of atoms          : 1908 (63110 expanded)
%              Number of equality atoms :   85 (1919 expanded)
%              Maximal formula depth    :   30 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f213,f218,f225,f230,f235,f240,f245,f250,f255,f376,f386,f426,f428,f430,f501,f506,f511,f516,f521,f526,f531,f536,f538,f690,f692,f694,f704,f706,f721,f751,f757,f761,f762,f764,f768,f894,f896,f897,f898,f899,f900,f901,f902])).

fof(f902,plain,
    ( ~ spl9_81
    | spl9_5
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_55 ),
    inference(avatar_split_clause,[],[f698,f499,f444,f447,f368,f371,f190,f702])).

fof(f702,plain,
    ( spl9_81
  <=> r4_tsep_1(sK0,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_81])])).

fof(f190,plain,
    ( spl9_5
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f371,plain,
    ( spl9_28
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f368,plain,
    ( spl9_27
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f447,plain,
    ( spl9_42
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f444,plain,
    ( spl9_41
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f499,plain,
    ( spl9_55
  <=> ! [X16,X15] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X15))
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK0)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,sK0)
        | sK0 != k1_tsep_1(sK0,X15,X16)
        | ~ r4_tsep_1(sK0,X15,X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_55])])).

fof(f698,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_55 ),
    inference(trivial_inequality_removal,[],[f697])).

fof(f697,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_55 ),
    inference(superposition,[],[f500,f93])).

fof(f93,plain,(
    sK0 = k1_tsep_1(sK0,sK3,sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
      | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2) )
    & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
      | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v5_pre_topc(sK2,sK0,sK1)
        & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(sK2) ) )
    & sK0 = k1_tsep_1(sK0,sK3,sK4)
    & m1_pre_topc(sK4,sK0)
    & v1_borsuk_1(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & v1_borsuk_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f61,f66,f65,f64,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) ) )
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK0,X1)
                          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & sK0 = k1_tsep_1(sK0,X3,X4)
                      & m1_pre_topc(X4,sK0)
                      & v1_borsuk_1(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & v1_borsuk_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK0,X1,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X2,sK0,X1)
                      | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(sK0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK0,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK0,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK0,X1,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                        & v5_pre_topc(X2,sK0,X1)
                        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
                        & v1_funct_1(X2) ) )
                    & sK0 = k1_tsep_1(sK0,X3,X4)
                    & m1_pre_topc(X4,sK0)
                    & v1_borsuk_1(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & v1_borsuk_1(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    | ~ v5_pre_topc(X2,sK0,sK1)
                    | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                      & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                      & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                      & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                      & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                      & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                      & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                      & v5_pre_topc(X2,sK0,sK1)
                      & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                      & v1_funct_1(X2) ) )
                  & sK0 = k1_tsep_1(sK0,X3,X4)
                  & m1_pre_topc(X4,sK0)
                  & v1_borsuk_1(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & v1_borsuk_1(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                  | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                  | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                  | ~ m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                  | ~ v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                  | ~ v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  | ~ v5_pre_topc(X2,sK0,sK1)
                  | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                  | ~ v1_funct_1(X2) )
                & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                    & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X4),X4,sK1)
                    & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                    & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK0,sK1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                    & v5_pre_topc(k2_tmap_1(sK0,sK1,X2,X3),X3,sK1)
                    & v1_funct_2(k2_tmap_1(sK0,sK1,X2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                    & v1_funct_1(k2_tmap_1(sK0,sK1,X2,X3)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                    & v5_pre_topc(X2,sK0,sK1)
                    & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
                    & v1_funct_1(X2) ) )
                & sK0 = k1_tsep_1(sK0,X3,X4)
                & m1_pre_topc(X4,sK0)
                & v1_borsuk_1(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & v1_borsuk_1(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
                | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
                | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
                | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3))
                | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                | ~ v5_pre_topc(sK2,sK0,sK1)
                | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
                | ~ v1_funct_1(sK2) )
              & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                  & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
                  & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                  & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
                  & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                  & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
                  & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                  & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3)) )
                | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                  & v5_pre_topc(sK2,sK0,sK1)
                  & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
                  & v1_funct_1(sK2) ) )
              & sK0 = k1_tsep_1(sK0,X3,X4)
              & m1_pre_topc(X4,sK0)
              & v1_borsuk_1(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & v1_borsuk_1(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
              | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
              | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
              | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
              | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
              | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
              | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3))
              | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              | ~ v5_pre_topc(sK2,sK0,sK1)
              | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
              | ~ v1_funct_1(sK2) )
            & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
                & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
                & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
                & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
                & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK1))))
                & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
                & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X3),u1_struct_0(X3),u1_struct_0(sK1))
                & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X3)) )
              | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
                & v5_pre_topc(sK2,sK0,sK1)
                & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
                & v1_funct_1(sK2) ) )
            & sK0 = k1_tsep_1(sK0,X3,X4)
            & m1_pre_topc(X4,sK0)
            & v1_borsuk_1(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & v1_borsuk_1(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
            | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
            | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
            | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
            | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
            | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
            | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            | ~ v5_pre_topc(sK2,sK0,sK1)
            | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
            | ~ v1_funct_1(sK2) )
          & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
              & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
              & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
              & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
              & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
              & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
              & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
              & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
            | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
              & v5_pre_topc(sK2,sK0,sK1)
              & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
              & v1_funct_1(sK2) ) )
          & sK0 = k1_tsep_1(sK0,sK3,X4)
          & m1_pre_topc(X4,sK0)
          & v1_borsuk_1(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & v1_borsuk_1(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
          | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
          | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
          | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
          | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
          | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
          | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          | ~ v5_pre_topc(sK2,sK0,sK1)
          | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          | ~ v1_funct_1(sK2) )
        & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK1))))
            & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X4),X4,sK1)
            & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X4),u1_struct_0(X4),u1_struct_0(sK1))
            & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X4))
            & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
            & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
            & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
            & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
          | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
            & v5_pre_topc(sK2,sK0,sK1)
            & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
            & v1_funct_1(sK2) ) )
        & sK0 = k1_tsep_1(sK0,sK3,X4)
        & m1_pre_topc(X4,sK0)
        & v1_borsuk_1(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(sK2,sK0,sK1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2) )
      & ( ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
          & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
          & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
          & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
          & m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
          & v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
          & v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
          & v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3)) )
        | ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v5_pre_topc(sK2,sK0,sK1)
          & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(sK2) ) )
      & sK0 = k1_tsep_1(sK0,sK3,sK4)
      & m1_pre_topc(sK4,sK0)
      & v1_borsuk_1(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,X0,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <~> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & v1_borsuk_1(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
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
                    ( ( m1_pre_topc(X3,X0)
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & v1_borsuk_1(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( k1_tsep_1(X0,X3,X4) = X0
                         => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                              & v5_pre_topc(X2,X0,X1)
                              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                              & v1_funct_1(X2) )
                          <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                              & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                              & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                              & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                              & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & v1_borsuk_1(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( k1_tsep_1(X0,X3,X4) = X0
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t133_tmap_1)).

fof(f500,plain,
    ( ! [X15,X16] :
        ( sK0 != k1_tsep_1(sK0,X15,X16)
        | v2_struct_0(X15)
        | ~ m1_pre_topc(X15,sK0)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X15))
        | ~ r4_tsep_1(sK0,X15,X16) )
    | ~ spl9_55 ),
    inference(avatar_component_clause,[],[f499])).

fof(f901,plain,
    ( ~ spl9_81
    | spl9_7
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f736,f509,f444,f447,f368,f371,f196,f702])).

fof(f196,plain,
    ( spl9_7
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f509,plain,
    ( spl9_57
  <=> ! [X11,X12] :
        ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X11),X11,sK1)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | sK0 != k1_tsep_1(sK0,X11,X12)
        | ~ r4_tsep_1(sK0,X11,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f736,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_57 ),
    inference(trivial_inequality_removal,[],[f735])).

fof(f735,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_57 ),
    inference(superposition,[],[f510,f93])).

fof(f510,plain,
    ( ! [X12,X11] :
        ( sK0 != k1_tsep_1(sK0,X11,X12)
        | v2_struct_0(X11)
        | ~ m1_pre_topc(X11,sK0)
        | v2_struct_0(X12)
        | ~ m1_pre_topc(X12,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X11),X11,sK1)
        | ~ r4_tsep_1(sK0,X11,X12) )
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f509])).

fof(f900,plain,
    ( ~ spl9_81
    | spl9_10
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f755,f524,f444,f447,f368,f371,f205,f702])).

fof(f205,plain,
    ( spl9_10
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f524,plain,
    ( spl9_60
  <=> ! [X5,X6] :
        ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X5),u1_struct_0(X5),u1_struct_0(sK1))
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | sK0 != k1_tsep_1(sK0,X6,X5)
        | ~ r4_tsep_1(sK0,X6,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f755,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_60 ),
    inference(trivial_inequality_removal,[],[f754])).

fof(f754,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_60 ),
    inference(superposition,[],[f525,f93])).

fof(f525,plain,
    ( ! [X6,X5] :
        ( sK0 != k1_tsep_1(sK0,X6,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X5),u1_struct_0(X5),u1_struct_0(sK1))
        | ~ r4_tsep_1(sK0,X6,X5) )
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f524])).

fof(f899,plain,
    ( ~ spl9_81
    | spl9_11
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_61 ),
    inference(avatar_split_clause,[],[f738,f529,f444,f447,f368,f371,f208,f702])).

fof(f208,plain,
    ( spl9_11
  <=> v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f529,plain,
    ( spl9_61
  <=> ! [X3,X4] :
        ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | sK0 != k1_tsep_1(sK0,X4,X3)
        | ~ r4_tsep_1(sK0,X4,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f738,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_61 ),
    inference(trivial_inequality_removal,[],[f737])).

fof(f737,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_61 ),
    inference(superposition,[],[f530,f93])).

fof(f530,plain,
    ( ! [X4,X3] :
        ( sK0 != k1_tsep_1(sK0,X4,X3)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
        | ~ r4_tsep_1(sK0,X4,X3) )
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f529])).

fof(f898,plain,
    ( ~ spl9_81
    | spl9_12
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_62 ),
    inference(avatar_split_clause,[],[f882,f534,f444,f447,f368,f371,f211,f702])).

fof(f211,plain,
    ( spl9_12
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f534,plain,
    ( spl9_62
  <=> ! [X1,X2] :
        ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | sK0 != k1_tsep_1(sK0,X2,X1)
        | ~ r4_tsep_1(sK0,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f882,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_62 ),
    inference(trivial_inequality_removal,[],[f881])).

fof(f881,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_62 ),
    inference(superposition,[],[f535,f93])).

fof(f535,plain,
    ( ! [X2,X1] :
        ( sK0 != k1_tsep_1(sK0,X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
        | ~ r4_tsep_1(sK0,X2,X1) )
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f534])).

fof(f897,plain,
    ( ~ spl9_81
    | spl9_6
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_56 ),
    inference(avatar_split_clause,[],[f753,f504,f444,f447,f368,f371,f193,f702])).

fof(f193,plain,
    ( spl9_6
  <=> v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f504,plain,
    ( spl9_56
  <=> ! [X13,X14] :
        ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | sK0 != k1_tsep_1(sK0,X13,X14)
        | ~ r4_tsep_1(sK0,X13,X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f753,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_56 ),
    inference(trivial_inequality_removal,[],[f752])).

fof(f752,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_56 ),
    inference(superposition,[],[f505,f93])).

fof(f505,plain,
    ( ! [X14,X13] :
        ( sK0 != k1_tsep_1(sK0,X13,X14)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,sK0)
        | v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
        | ~ r4_tsep_1(sK0,X13,X14) )
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f504])).

fof(f896,plain,(
    spl9_4 ),
    inference(avatar_contradiction_clause,[],[f895])).

fof(f895,plain,
    ( $false
    | spl9_4 ),
    inference(subsumption_resolution,[],[f86,f188])).

fof(f188,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl9_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f67])).

fof(f894,plain,
    ( ~ spl9_7
    | ~ spl9_6
    | ~ spl9_5
    | ~ spl9_81
    | ~ spl9_42
    | spl9_41
    | ~ spl9_8
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f893,f374,f199,f444,f447,f702,f190,f193,f196])).

fof(f199,plain,
    ( spl9_8
  <=> m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f374,plain,
    ( spl9_29
  <=> ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | sK0 != k1_tsep_1(sK0,X0,sK4)
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f893,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl9_8
    | ~ spl9_29 ),
    inference(trivial_inequality_removal,[],[f892])).

fof(f892,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl9_8
    | ~ spl9_29 ),
    inference(forward_demodulation,[],[f884,f93])).

fof(f884,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | sK0 != k1_tsep_1(sK0,sK3,sK4)
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ spl9_8
    | ~ spl9_29 ),
    inference(resolution,[],[f375,f238])).

fof(f238,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f199])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | sK0 != k1_tsep_1(sK0,X0,sK4)
        | ~ r4_tsep_1(sK0,X0,sK4)
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1) )
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f374])).

fof(f768,plain,(
    ~ spl9_27 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | ~ spl9_27 ),
    inference(subsumption_resolution,[],[f90,f369])).

fof(f369,plain,
    ( v2_struct_0(sK4)
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f368])).

fof(f90,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f764,plain,(
    ~ spl9_41 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | ~ spl9_41 ),
    inference(subsumption_resolution,[],[f87,f445])).

fof(f445,plain,
    ( v2_struct_0(sK3)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f444])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f762,plain,
    ( ~ spl9_81
    | spl9_8
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f759,f514,f444,f447,f368,f371,f199,f702])).

fof(f514,plain,
    ( spl9_58
  <=> ! [X9,X10] :
        ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0)
        | sK0 != k1_tsep_1(sK0,X9,X10)
        | ~ r4_tsep_1(sK0,X9,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f759,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_58 ),
    inference(trivial_inequality_removal,[],[f758])).

fof(f758,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_58 ),
    inference(superposition,[],[f515,f93])).

fof(f515,plain,
    ( ! [X10,X9] :
        ( sK0 != k1_tsep_1(sK0,X9,X10)
        | v2_struct_0(X9)
        | ~ m1_pre_topc(X9,sK0)
        | v2_struct_0(X10)
        | ~ m1_pre_topc(X10,sK0)
        | m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
        | ~ r4_tsep_1(sK0,X9,X10) )
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f514])).

fof(f761,plain,(
    spl9_83 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | spl9_83 ),
    inference(subsumption_resolution,[],[f88,f747])).

fof(f747,plain,
    ( ~ v1_borsuk_1(sK3,sK0)
    | spl9_83 ),
    inference(avatar_component_clause,[],[f746])).

fof(f746,plain,
    ( spl9_83
  <=> v1_borsuk_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_83])])).

fof(f88,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f757,plain,(
    spl9_84 ),
    inference(avatar_contradiction_clause,[],[f756])).

fof(f756,plain,
    ( $false
    | spl9_84 ),
    inference(subsumption_resolution,[],[f91,f750])).

fof(f750,plain,
    ( ~ v1_borsuk_1(sK4,sK0)
    | spl9_84 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl9_84
  <=> v1_borsuk_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f91,plain,(
    v1_borsuk_1(sK4,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f751,plain,
    ( spl9_21
    | ~ spl9_22
    | ~ spl9_23
    | ~ spl9_83
    | ~ spl9_42
    | ~ spl9_84
    | ~ spl9_28
    | spl9_81 ),
    inference(avatar_split_clause,[],[f740,f702,f371,f749,f447,f746,f356,f353,f350])).

fof(f350,plain,
    ( spl9_21
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f353,plain,
    ( spl9_22
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f356,plain,
    ( spl9_23
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f740,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ v1_borsuk_1(sK4,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_borsuk_1(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl9_81 ),
    inference(resolution,[],[f703,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( r4_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_tsep_1(X0,X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0) )
          | ~ m1_pre_topc(X1,X0)
          | ~ v1_borsuk_1(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v1_borsuk_1(X1,X0) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0) )
             => r4_tsep_1(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tsep_1)).

fof(f703,plain,
    ( ~ r4_tsep_1(sK0,sK3,sK4)
    | spl9_81 ),
    inference(avatar_component_clause,[],[f702])).

fof(f721,plain,(
    spl9_42 ),
    inference(avatar_contradiction_clause,[],[f720])).

fof(f720,plain,
    ( $false
    | spl9_42 ),
    inference(subsumption_resolution,[],[f89,f448])).

fof(f448,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | spl9_42 ),
    inference(avatar_component_clause,[],[f447])).

fof(f89,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f706,plain,(
    spl9_28 ),
    inference(avatar_contradiction_clause,[],[f705])).

fof(f705,plain,
    ( $false
    | spl9_28 ),
    inference(subsumption_resolution,[],[f92,f372])).

fof(f372,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | spl9_28 ),
    inference(avatar_component_clause,[],[f371])).

fof(f92,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f704,plain,
    ( ~ spl9_81
    | spl9_9
    | ~ spl9_28
    | spl9_27
    | ~ spl9_42
    | spl9_41
    | ~ spl9_59 ),
    inference(avatar_split_clause,[],[f700,f519,f444,f447,f368,f371,f202,f702])).

fof(f202,plain,
    ( spl9_9
  <=> v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f519,plain,
    ( spl9_59
  <=> ! [X7,X8] :
        ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X7))
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | sK0 != k1_tsep_1(sK0,X8,X7)
        | ~ r4_tsep_1(sK0,X8,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_59])])).

fof(f700,plain,
    ( v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_59 ),
    inference(trivial_inequality_removal,[],[f699])).

fof(f699,plain,
    ( sK0 != sK0
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ r4_tsep_1(sK0,sK3,sK4)
    | ~ spl9_59 ),
    inference(superposition,[],[f520,f93])).

fof(f520,plain,
    ( ! [X8,X7] :
        ( sK0 != k1_tsep_1(sK0,X8,X7)
        | v2_struct_0(X8)
        | ~ m1_pre_topc(X8,sK0)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X7))
        | ~ r4_tsep_1(sK0,X8,X7) )
    | ~ spl9_59 ),
    inference(avatar_component_clause,[],[f519])).

fof(f694,plain,(
    ~ spl9_21 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | ~ spl9_21 ),
    inference(subsumption_resolution,[],[f78,f351])).

fof(f351,plain,
    ( v2_struct_0(sK0)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f350])).

fof(f78,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f692,plain,(
    spl9_23 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl9_23 ),
    inference(subsumption_resolution,[],[f80,f357])).

fof(f357,plain,
    ( ~ l1_pre_topc(sK0)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f356])).

fof(f80,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f690,plain,(
    spl9_22 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | spl9_22 ),
    inference(subsumption_resolution,[],[f79,f354])).

fof(f354,plain,
    ( ~ v2_pre_topc(sK0)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f353])).

fof(f79,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f538,plain,(
    ~ spl9_24 ),
    inference(avatar_contradiction_clause,[],[f537])).

fof(f537,plain,
    ( $false
    | ~ spl9_24 ),
    inference(subsumption_resolution,[],[f81,f360])).

fof(f360,plain,
    ( v2_struct_0(sK1)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl9_24
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f536,plain,
    ( ~ spl9_3
    | spl9_62 ),
    inference(avatar_split_clause,[],[f532,f534,f184])).

fof(f184,plain,
    ( spl9_3
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f532,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X2,X1)
      | sK0 != k1_tsep_1(sK0,X2,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f322])).

fof(f322,plain,(
    ! [X2,X1] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X2,X1)
      | sK0 != k1_tsep_1(sK0,X2,X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X2,sK0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f169])).

fof(f169,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                        & ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
                          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          | ~ v5_pre_topc(X2,X0,X1)
                          | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          | ~ v1_funct_1(X2) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v5_pre_topc(X2,X0,X1)
                          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X2) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) )
                      | ~ r4_tsep_1(X0,X3,X4)
                      | k1_tsep_1(X0,X3,X4) != X0
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( r4_tsep_1(X0,X3,X4)
                          & k1_tsep_1(X0,X3,X4) = X0 )
                       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v5_pre_topc(X2,X0,X1)
                            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X2) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
                            & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f82,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f85,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f67])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f531,plain,
    ( ~ spl9_3
    | spl9_61 ),
    inference(avatar_split_clause,[],[f527,f529,f184])).

fof(f527,plain,(
    ! [X4,X3] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X4,X3)
      | sK0 != k1_tsep_1(sK0,X4,X3)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f323])).

fof(f323,plain,(
    ! [X4,X3] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X3),X3,sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X4,X3)
      | sK0 != k1_tsep_1(sK0,X4,X3)
      | ~ m1_pre_topc(X3,sK0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X4,sK0)
      | v2_struct_0(X4)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f170])).

fof(f170,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f526,plain,
    ( ~ spl9_3
    | spl9_60 ),
    inference(avatar_split_clause,[],[f522,f524,f184])).

fof(f522,plain,(
    ! [X6,X5] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X5),u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X6,X5)
      | sK0 != k1_tsep_1(sK0,X6,X5)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f324])).

fof(f324,plain,(
    ! [X6,X5] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X5),u1_struct_0(X5),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X6,X5)
      | sK0 != k1_tsep_1(sK0,X6,X5)
      | ~ m1_pre_topc(X5,sK0)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X6,sK0)
      | v2_struct_0(X6)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f171])).

fof(f171,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f521,plain,
    ( ~ spl9_3
    | spl9_59 ),
    inference(avatar_split_clause,[],[f517,f519,f184])).

fof(f517,plain,(
    ! [X8,X7] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X7))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X8,X7)
      | sK0 != k1_tsep_1(sK0,X8,X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X8,sK0)
      | v2_struct_0(X8) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f325])).

fof(f325,plain,(
    ! [X8,X7] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X7))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X8,X7)
      | sK0 != k1_tsep_1(sK0,X8,X7)
      | ~ m1_pre_topc(X7,sK0)
      | v2_struct_0(X7)
      | ~ m1_pre_topc(X8,sK0)
      | v2_struct_0(X8)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f172])).

fof(f172,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f516,plain,
    ( ~ spl9_3
    | spl9_58 ),
    inference(avatar_split_clause,[],[f512,f514,f184])).

fof(f512,plain,(
    ! [X10,X9] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X9,X10)
      | sK0 != k1_tsep_1(sK0,X9,X10)
      | ~ m1_pre_topc(X10,sK0)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,sK0)
      | v2_struct_0(X9) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f326])).

fof(f326,plain,(
    ! [X10,X9] :
      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK1))))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X9,X10)
      | sK0 != k1_tsep_1(sK0,X9,X10)
      | ~ m1_pre_topc(X10,sK0)
      | v2_struct_0(X10)
      | ~ m1_pre_topc(X9,sK0)
      | v2_struct_0(X9)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f173])).

fof(f173,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f511,plain,
    ( ~ spl9_3
    | spl9_57 ),
    inference(avatar_split_clause,[],[f507,f509,f184])).

fof(f507,plain,(
    ! [X12,X11] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X11),X11,sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X11,X12)
      | sK0 != k1_tsep_1(sK0,X11,X12)
      | ~ m1_pre_topc(X12,sK0)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X11,sK0)
      | v2_struct_0(X11) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f327])).

fof(f327,plain,(
    ! [X12,X11] :
      ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X11),X11,sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X11,X12)
      | sK0 != k1_tsep_1(sK0,X11,X12)
      | ~ m1_pre_topc(X12,sK0)
      | v2_struct_0(X12)
      | ~ m1_pre_topc(X11,sK0)
      | v2_struct_0(X11)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f174])).

fof(f174,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f506,plain,
    ( ~ spl9_3
    | spl9_56 ),
    inference(avatar_split_clause,[],[f502,f504,f184])).

fof(f502,plain,(
    ! [X14,X13] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X13,X14)
      | sK0 != k1_tsep_1(sK0,X13,X14)
      | ~ m1_pre_topc(X14,sK0)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,sK0)
      | v2_struct_0(X13) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f328])).

fof(f328,plain,(
    ! [X14,X13] :
      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X13),u1_struct_0(X13),u1_struct_0(sK1))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X13,X14)
      | sK0 != k1_tsep_1(sK0,X13,X14)
      | ~ m1_pre_topc(X14,sK0)
      | v2_struct_0(X14)
      | ~ m1_pre_topc(X13,sK0)
      | v2_struct_0(X13)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f175])).

fof(f175,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f501,plain,
    ( ~ spl9_3
    | spl9_55 ),
    inference(avatar_split_clause,[],[f497,f499,f184])).

fof(f497,plain,(
    ! [X15,X16] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X15))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ r4_tsep_1(sK0,X15,X16)
      | sK0 != k1_tsep_1(sK0,X15,X16)
      | ~ m1_pre_topc(X16,sK0)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X15,sK0)
      | v2_struct_0(X15) ) ),
    inference(global_subsumption,[],[f78,f79,f80,f81,f84,f85,f82,f83,f329])).

fof(f329,plain,(
    ! [X15,X16] :
      ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X15))
      | ~ v5_pre_topc(sK2,sK0,sK1)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ v1_funct_1(sK2)
      | ~ r4_tsep_1(sK0,X15,X16)
      | sK0 != k1_tsep_1(sK0,X15,X16)
      | ~ m1_pre_topc(X16,sK0)
      | v2_struct_0(X16)
      | ~ m1_pre_topc(X15,sK0)
      | v2_struct_0(X15)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f86,f176])).

fof(f176,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f430,plain,(
    spl9_26 ),
    inference(avatar_contradiction_clause,[],[f429])).

fof(f429,plain,
    ( $false
    | spl9_26 ),
    inference(subsumption_resolution,[],[f83,f366])).

fof(f366,plain,
    ( ~ l1_pre_topc(sK1)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f365])).

fof(f365,plain,
    ( spl9_26
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f428,plain,(
    spl9_25 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | spl9_25 ),
    inference(subsumption_resolution,[],[f82,f363])).

fof(f363,plain,
    ( ~ v2_pre_topc(sK1)
    | spl9_25 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl9_25
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f426,plain,(
    spl9_2 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | spl9_2 ),
    inference(subsumption_resolution,[],[f85,f182])).

fof(f182,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl9_2
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f386,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f84,f179])).

fof(f179,plain,
    ( ~ v1_funct_1(sK2)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl9_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f376,plain,
    ( spl9_21
    | ~ spl9_22
    | ~ spl9_23
    | spl9_24
    | ~ spl9_25
    | ~ spl9_26
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_27
    | ~ spl9_28
    | spl9_29
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | spl9_3
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f337,f211,f184,f208,f205,f202,f374,f371,f368,f187,f181,f178,f365,f362,f359,f356,f353,f350])).

fof(f337,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,sK0,sK1)
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
        | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,X0),X0,sK1)
        | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,X0),u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,X0))
        | ~ r4_tsep_1(sK0,X0,sK4)
        | sK0 != k1_tsep_1(sK0,X0,sK4)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK4)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(sK1)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl9_12 ),
    inference(resolution,[],[f215,f143])).

fof(f143,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X4))
      | ~ m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ r4_tsep_1(X0,X3,X4)
      | k1_tsep_1(X0,X3,X4) != X0
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f215,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f211])).

fof(f255,plain,
    ( spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f96,f190,f184])).

fof(f96,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f250,plain,
    ( spl9_3
    | spl9_6 ),
    inference(avatar_split_clause,[],[f100,f193,f184])).

fof(f100,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f245,plain,
    ( spl9_3
    | spl9_7 ),
    inference(avatar_split_clause,[],[f104,f196,f184])).

fof(f104,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f240,plain,
    ( spl9_3
    | spl9_8 ),
    inference(avatar_split_clause,[],[f108,f199,f184])).

fof(f108,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f235,plain,
    ( spl9_3
    | spl9_9 ),
    inference(avatar_split_clause,[],[f112,f202,f184])).

fof(f112,plain,
    ( v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f230,plain,
    ( spl9_3
    | spl9_10 ),
    inference(avatar_split_clause,[],[f116,f205,f184])).

fof(f116,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f225,plain,
    ( spl9_3
    | spl9_11 ),
    inference(avatar_split_clause,[],[f120,f208,f184])).

fof(f120,plain,
    ( v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f218,plain,
    ( spl9_3
    | spl9_12 ),
    inference(avatar_split_clause,[],[f124,f211,f184])).

fof(f124,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f213,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | ~ spl9_6
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f126,f211,f208,f205,f202,f199,f196,f193,f190,f187,f184,f181,f178])).

fof(f126,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK4),sK4,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK4),u1_struct_0(sK4),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK4))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tmap_1(sK0,sK1,sK2,sK3),sK3,sK1)
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK2,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

%------------------------------------------------------------------------------
