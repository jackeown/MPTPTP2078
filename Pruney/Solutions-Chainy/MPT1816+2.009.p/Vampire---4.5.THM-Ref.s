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
% DateTime   : Thu Dec  3 13:19:46 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  342 (4045 expanded)
%              Number of leaves         :   39 (1625 expanded)
%              Depth                    :   35
%              Number of atoms          : 2319 (137678 expanded)
%              Number of equality atoms :   66 (4169 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1648,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f181,f187,f203,f692,f743,f746,f943,f994,f1318,f1346,f1373,f1375,f1377,f1498,f1509,f1513,f1573,f1604,f1625,f1634,f1636,f1639,f1647])).

fof(f1647,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f1646])).

fof(f1646,plain,
    ( $false
    | spl7_10 ),
    inference(subsumption_resolution,[],[f1645,f214])).

fof(f214,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f55,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
      | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4) )
    & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
      | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v5_pre_topc(sK4,sK2,sK3)
        & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(sK4) ) )
    & r4_tsep_1(sK2,sK5,sK6)
    & sK2 = k1_tsep_1(sK2,sK5,sK6)
    & m1_pre_topc(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f39,f44,f43,f42,f41,f40])).

fof(f40,plain,
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
                        & r4_tsep_1(X0,X3,X4)
                        & k1_tsep_1(X0,X3,X4) = X0
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
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
                      ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        | ~ v5_pre_topc(X2,sK2,X1)
                        | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        | ~ v1_funct_1(X2) )
                      & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                          & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                        | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                          & v5_pre_topc(X2,sK2,X1)
                          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                          & v1_funct_1(X2) ) )
                      & r4_tsep_1(sK2,X3,X4)
                      & sK2 = k1_tsep_1(sK2,X3,X4)
                      & m1_pre_topc(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                      | ~ m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                      | ~ v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))
                      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                      | ~ v5_pre_topc(X2,sK2,X1)
                      | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                      | ~ v1_funct_1(X2) )
                    & ( ( m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4))
                        & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1)
                        & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) )
                      | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
                        & v5_pre_topc(X2,sK2,X1)
                        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
                        & v1_funct_1(X2) ) )
                    & r4_tsep_1(sK2,X3,X4)
                    & sK2 = k1_tsep_1(sK2,X3,X4)
                    & m1_pre_topc(X4,sK2)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    | ~ v5_pre_topc(X2,sK2,sK3)
                    | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    | ~ v1_funct_1(X2) )
                  & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                      & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                      & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                      & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                      & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                    | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                      & v5_pre_topc(X2,sK2,sK3)
                      & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                      & v1_funct_1(X2) ) )
                  & r4_tsep_1(sK2,X3,X4)
                  & sK2 = k1_tsep_1(sK2,X3,X4)
                  & m1_pre_topc(X4,sK2)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                  | ~ m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                  | ~ v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  | ~ v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  | ~ v5_pre_topc(X2,sK2,sK3)
                  | ~ v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                  | ~ v1_funct_1(X2) )
                & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4))
                    & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                    & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3)
                    & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3))
                    & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) )
                  | ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                    & v5_pre_topc(X2,sK2,sK3)
                    & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
                    & v1_funct_1(X2) ) )
                & r4_tsep_1(sK2,X3,X4)
                & sK2 = k1_tsep_1(sK2,X3,X4)
                & m1_pre_topc(X4,sK2)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
                | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                | ~ v5_pre_topc(sK4,sK2,sK3)
                | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                | ~ v1_funct_1(sK4) )
              & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                  & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                  & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
                | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                  & v5_pre_topc(sK4,sK2,sK3)
                  & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                  & v1_funct_1(sK4) ) )
              & r4_tsep_1(sK2,X3,X4)
              & sK2 = k1_tsep_1(sK2,X3,X4)
              & m1_pre_topc(X4,sK2)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
              | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
              | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))
              | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              | ~ v5_pre_topc(sK4,sK2,sK3)
              | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              | ~ v1_funct_1(sK4) )
            & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
                & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3)
                & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) )
              | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
                & v5_pre_topc(sK4,sK2,sK3)
                & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
                & v1_funct_1(sK4) ) )
            & r4_tsep_1(sK2,X3,X4)
            & sK2 = k1_tsep_1(sK2,X3,X4)
            & m1_pre_topc(X4,sK2)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
            | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            | ~ v5_pre_topc(sK4,sK2,sK3)
            | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            | ~ v1_funct_1(sK4) )
          & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
              & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
              & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
              & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
              & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
            | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
              & v5_pre_topc(sK4,sK2,sK3)
              & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
              & v1_funct_1(sK4) ) )
          & r4_tsep_1(sK2,sK5,X4)
          & sK2 = k1_tsep_1(sK2,sK5,X4)
          & m1_pre_topc(X4,sK2)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
          | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
          | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          | ~ v5_pre_topc(sK4,sK2,sK3)
          | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          | ~ v1_funct_1(sK4) )
        & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4))
            & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
            & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
            & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
            & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
          | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
            & v5_pre_topc(sK4,sK2,sK3)
            & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
            & v1_funct_1(sK4) ) )
        & r4_tsep_1(sK2,sK5,X4)
        & sK2 = k1_tsep_1(sK2,sK5,X4)
        & m1_pre_topc(X4,sK2)
        & ~ v2_struct_0(X4) )
   => ( ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
        | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v5_pre_topc(sK4,sK2,sK3)
        | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK4) )
      & ( ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
          & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
          & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
        | ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v5_pre_topc(sK4,sK2,sK3)
          & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(sK4) ) )
      & r4_tsep_1(sK2,sK5,sK6)
      & sK2 = k1_tsep_1(sK2,sK5,sK6)
      & m1_pre_topc(sK6,sK2)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
                      & r4_tsep_1(X0,X3,X4)
                      & k1_tsep_1(X0,X3,X4) = X0
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).

fof(f1645,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f1644,f215])).

fof(f215,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f58,f101])).

fof(f58,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f1644,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f1643,f59])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f1643,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f1642,f60])).

fof(f60,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f1642,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f1641,f61])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1641,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_10 ),
    inference(subsumption_resolution,[],[f1640,f223])).

fof(f223,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f222,f101])).

fof(f222,plain,(
    l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f221,f55])).

fof(f221,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f65,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f65,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1640,plain,
    ( ~ l1_struct_0(sK6)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_10 ),
    inference(resolution,[],[f172,f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(f172,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl7_10
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f1639,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f1638])).

fof(f1638,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f1637,f219])).

fof(f219,plain,(
    l1_struct_0(sK5) ),
    inference(resolution,[],[f218,f101])).

fof(f218,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f217,f55])).

fof(f217,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f63,f103])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f1637,plain,
    ( ~ l1_struct_0(sK5)
    | spl7_8 ),
    inference(resolution,[],[f164,f264])).

fof(f264,plain,(
    ! [X9] :
      ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3))))
      | ~ l1_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f263,f214])).

fof(f263,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3))))
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f262,f215])).

fof(f262,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3))))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f261,f59])).

fof(f261,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3))))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f232,f60])).

fof(f232,plain,(
    ! [X9] :
      ( ~ l1_struct_0(X9)
      | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f164,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl7_8
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1636,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f1635])).

fof(f1635,plain,
    ( $false
    | spl7_9 ),
    inference(subsumption_resolution,[],[f272,f168])).

fof(f168,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_9
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f272,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) ),
    inference(resolution,[],[f260,f223])).

fof(f260,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8)) ) ),
    inference(subsumption_resolution,[],[f259,f214])).

fof(f259,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8))
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f258,f215])).

fof(f258,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f257,f59])).

fof(f257,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f231,f60])).

fof(f231,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1634,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f1633])).

fof(f1633,plain,
    ( $false
    | spl7_12 ),
    inference(subsumption_resolution,[],[f1632,f223])).

fof(f1632,plain,
    ( ~ l1_struct_0(sK6)
    | spl7_12 ),
    inference(resolution,[],[f180,f264])).

fof(f180,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl7_12
  <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1625,plain,(
    spl7_6 ),
    inference(avatar_contradiction_clause,[],[f1624])).

fof(f1624,plain,
    ( $false
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1623,f214])).

fof(f1623,plain,
    ( ~ l1_struct_0(sK2)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1622,f215])).

fof(f1622,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1621,f59])).

fof(f1621,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1620,f60])).

fof(f1620,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1619,f61])).

fof(f1619,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_6 ),
    inference(subsumption_resolution,[],[f1618,f219])).

fof(f1618,plain,
    ( ~ l1_struct_0(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_6 ),
    inference(resolution,[],[f156,f127])).

fof(f156,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_6
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f1604,plain,
    ( spl7_11
    | ~ spl7_59 ),
    inference(avatar_contradiction_clause,[],[f1603])).

fof(f1603,plain,
    ( $false
    | spl7_11
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f1602,f64])).

fof(f64,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f1602,plain,
    ( v2_struct_0(sK6)
    | spl7_11
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f1600,f65])).

fof(f1600,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | spl7_11
    | ~ spl7_59 ),
    inference(resolution,[],[f1345,f176])).

fof(f176,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl7_11
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f1345,plain,
    ( ! [X7] :
        ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
        | ~ m1_pre_topc(X7,sK2)
        | v2_struct_0(X7) )
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f1344])).

fof(f1344,plain,
    ( spl7_59
  <=> ! [X7] :
        ( ~ m1_pre_topc(X7,sK2)
        | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
        | v2_struct_0(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f1573,plain,
    ( spl7_7
    | ~ spl7_25
    | ~ spl7_35
    | ~ spl7_47 ),
    inference(avatar_contradiction_clause,[],[f1572])).

fof(f1572,plain,
    ( $false
    | spl7_7
    | ~ spl7_25
    | ~ spl7_35
    | ~ spl7_47 ),
    inference(subsumption_resolution,[],[f1538,f160])).

fof(f160,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_7
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f1538,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_25
    | ~ spl7_35
    | ~ spl7_47 ),
    inference(resolution,[],[f1515,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
        | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
        | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
        | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
        | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
      & ( ( m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
          & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
          & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
          & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
          & v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( ( sP0(X1,X3,X4,X0,X2)
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
      & ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) )
        | ~ sP0(X1,X3,X4,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X1,X3,X4,X0,X2] :
      ( sP0(X1,X3,X4,X0,X2)
    <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
        & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1515,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_25
    | ~ spl7_35
    | ~ spl7_47 ),
    inference(forward_demodulation,[],[f942,f1273])).

fof(f1273,plain,
    ( sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1272,f59])).

fof(f1272,plain,
    ( sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ v1_funct_1(sK4)
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1271,f60])).

fof(f1271,plain,
    ( sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1270,f61])).

fof(f1270,plain,
    ( sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1269,f644])).

fof(f644,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f643])).

fof(f643,plain,
    ( spl7_25
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1269,plain,
    ( sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1260,f214])).

fof(f1260,plain,
    ( ~ l1_struct_0(sK2)
    | sK4 = k2_tmap_1(sK2,sK3,sK4,sK2)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ spl7_35 ),
    inference(resolution,[],[f517,f742])).

fof(f742,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f740])).

fof(f740,plain,
    ( spl7_35
  <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f517,plain,(
    ! [X23,X22] :
      ( ~ r2_funct_2(u1_struct_0(X22),u1_struct_0(sK3),X23,k2_tmap_1(sK2,sK3,sK4,X22))
      | ~ l1_struct_0(X22)
      | k2_tmap_1(sK2,sK3,sK4,X22) = X23
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X22),u1_struct_0(X22),u1_struct_0(sK3))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(sK3))))
      | ~ v1_funct_2(X23,u1_struct_0(X22),u1_struct_0(sK3))
      | ~ v1_funct_1(X23) ) ),
    inference(subsumption_resolution,[],[f483,f260])).

fof(f483,plain,(
    ! [X23,X22] :
      ( ~ l1_struct_0(X22)
      | ~ r2_funct_2(u1_struct_0(X22),u1_struct_0(sK3),X23,k2_tmap_1(sK2,sK3,sK4,X22))
      | k2_tmap_1(sK2,sK3,sK4,X22) = X23
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X22),u1_struct_0(X22),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(sK3))))
      | ~ v1_funct_2(X23,u1_struct_0(X22),u1_struct_0(sK3))
      | ~ v1_funct_1(X23) ) ),
    inference(resolution,[],[f264,f129])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_funct_2(X0,X1,X2,X3)
      | X2 = X3
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f942,plain,
    ( sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5)
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f940])).

fof(f940,plain,
    ( spl7_47
  <=> sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1513,plain,
    ( ~ spl7_3
    | ~ spl7_25
    | ~ spl7_35
    | spl7_46 ),
    inference(avatar_contradiction_clause,[],[f1512])).

fof(f1512,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_35
    | spl7_46 ),
    inference(subsumption_resolution,[],[f1511,f143])).

fof(f143,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_3
  <=> v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1511,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_46 ),
    inference(forward_demodulation,[],[f1510,f1273])).

fof(f1510,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_46 ),
    inference(forward_demodulation,[],[f938,f1273])).

fof(f938,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3)
    | spl7_46 ),
    inference(avatar_component_clause,[],[f936])).

fof(f936,plain,
    ( spl7_46
  <=> v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1509,plain,
    ( ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(avatar_contradiction_clause,[],[f1508])).

fof(f1508,plain,
    ( $false
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(subsumption_resolution,[],[f1507,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f1507,plain,
    ( v2_struct_0(sK5)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(subsumption_resolution,[],[f1506,f63])).

fof(f1506,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(subsumption_resolution,[],[f1505,f64])).

fof(f1505,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(subsumption_resolution,[],[f1504,f65])).

fof(f1504,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(subsumption_resolution,[],[f1503,f67])).

fof(f67,plain,(
    r4_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f1503,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(resolution,[],[f1286,f248])).

fof(f248,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f247,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f247,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f246,f54])).

fof(f54,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f246,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f245,f55])).

fof(f245,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f244,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f244,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f243,f57])).

fof(f57,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f243,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f242,f58])).

fof(f242,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f241,f59])).

fof(f241,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f226,f60])).

fof(f226,plain,(
    ! [X2,X3] :
      ( sP1(X2,sK2,sK4,X3,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ r4_tsep_1(sK2,X2,X3)
      | ~ m1_pre_topc(X3,sK2)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,sK2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f119])).

fof(f119,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X2,X0,X4,X3,X1)
      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ r4_tsep_1(X0,X2,X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( sP1(X2,X0,X4,X3,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f36,f35])).

fof(f36,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
      <=> sP0(X1,X3,X4,X0,X2) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                      <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                          & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                          & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ r4_tsep_1(X0,X2,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( r4_tsep_1(X0,X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
                        <=> ( m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X3))
                            & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                            & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1)
                            & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1))
                            & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).

fof(f1286,plain,
    ( ~ sP1(sK5,sK2,sK4,sK6,sK3)
    | ~ spl7_25
    | ~ spl7_35
    | spl7_44 ),
    inference(backward_demodulation,[],[f930,f1273])).

fof(f930,plain,
    ( ~ sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3)
    | spl7_44 ),
    inference(avatar_component_clause,[],[f928])).

fof(f928,plain,
    ( spl7_44
  <=> sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f1498,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f1497])).

fof(f1497,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f271,f152])).

fof(f152,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_5
  <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f271,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) ),
    inference(resolution,[],[f260,f219])).

fof(f1377,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f1376])).

fof(f1376,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f140,f60])).

fof(f140,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_2
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1375,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f1374])).

fof(f1374,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f148,f61])).

fof(f148,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1373,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f1372])).

fof(f1372,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f136,f59])).

fof(f136,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f1346,plain,
    ( ~ spl7_3
    | spl7_59 ),
    inference(avatar_split_clause,[],[f1342,f1344,f142])).

fof(f1342,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f1341,f53])).

fof(f1341,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1340,f54])).

fof(f1340,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1339,f55])).

fof(f1339,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1338,f56])).

fof(f1338,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1337,f57])).

fof(f1337,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1336,f58])).

fof(f1336,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f1335,f59])).

fof(f1335,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f230,f60])).

fof(f230,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK2)
      | v2_struct_0(X7)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3)
      | ~ v5_pre_topc(sK4,sK2,sK3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f1318,plain,
    ( spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f1317])).

fof(f1317,plain,
    ( $false
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1289,f144])).

fof(f144,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f142])).

fof(f1289,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(backward_demodulation,[],[f1028,f1273])).

fof(f1028,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(forward_demodulation,[],[f1027,f66])).

fof(f66,plain,(
    sK2 = k1_tsep_1(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f1027,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1026,f67])).

fof(f1026,plain,
    ( ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1025,f62])).

fof(f1025,plain,
    ( v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1024,f63])).

fof(f1024,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1023,f64])).

fof(f1023,plain,
    ( v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f1018,f65])).

fof(f1018,plain,
    ( ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK6)
    | ~ m1_pre_topc(sK5,sK2)
    | v2_struct_0(sK5)
    | ~ r4_tsep_1(sK2,sK5,sK6)
    | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(resolution,[],[f617,f763])).

fof(f763,plain,
    ( sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f762,f167])).

fof(f167,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f166])).

fof(f762,plain,
    ( ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f761,f171])).

fof(f171,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f170])).

fof(f761,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f756,f175])).

fof(f175,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f756,plain,
    ( ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | sP0(sK3,sK6,sK4,sK2,sK5)
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_12 ),
    inference(resolution,[],[f288,f179])).

fof(f179,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5) )
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f287,f151])).

fof(f151,plain,
    ( v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f286,f155])).

fof(f155,plain,
    ( v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f154])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f275,f159])).

fof(f159,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f275,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0))
        | sP0(sK3,X0,sK4,sK2,sK5)
        | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
        | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f163,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0))))
      | ~ m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X1))
      | sP0(X0,X1,X2,X3,X4)
      | ~ v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)
      | ~ v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(X3,X0,X2,X4)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f163,plain,
    ( m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f162])).

fof(f617,plain,(
    ! [X4,X5] :
      ( ~ sP0(sK3,X5,sK4,sK2,X4)
      | ~ m1_pre_topc(X5,sK2)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X4,sK2)
      | v2_struct_0(X4)
      | ~ r4_tsep_1(sK2,X4,X5)
      | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X4,X5)),k1_tsep_1(sK2,X4,X5),sK3) ) ),
    inference(resolution,[],[f248,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,X4)
      | ~ sP0(X4,X3,X2,X1,X0)
      | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
            & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
            & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
            & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) )
          | ~ sP0(X4,X3,X2,X1,X0) )
        & ( sP0(X4,X3,X2,X1,X0)
          | ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
          | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
          | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
          | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) ) )
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X4,X3,X1] :
      ( ( ( ( m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
            & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
            & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
            & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) )
          | ~ sP0(X1,X3,X4,X0,X2) )
        & ( sP0(X1,X3,X4,X0,X2)
          | ~ m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
          | ~ v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1)
          | ~ v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
          | ~ v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))) ) )
      | ~ sP1(X2,X0,X4,X3,X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f994,plain,
    ( ~ spl7_25
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f993])).

fof(f993,plain,
    ( $false
    | ~ spl7_25
    | spl7_45 ),
    inference(subsumption_resolution,[],[f992,f214])).

fof(f992,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl7_25
    | spl7_45 ),
    inference(resolution,[],[f991,f264])).

fof(f991,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl7_25
    | spl7_45 ),
    inference(subsumption_resolution,[],[f990,f215])).

fof(f990,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK3)
    | ~ spl7_25
    | spl7_45 ),
    inference(subsumption_resolution,[],[f989,f269])).

fof(f269,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) ),
    inference(resolution,[],[f260,f214])).

fof(f989,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ l1_struct_0(sK3)
    | ~ spl7_25
    | spl7_45 ),
    inference(subsumption_resolution,[],[f988,f644])).

fof(f988,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ l1_struct_0(sK3)
    | spl7_45 ),
    inference(subsumption_resolution,[],[f987,f214])).

fof(f987,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ l1_struct_0(sK3)
    | spl7_45 ),
    inference(duplicate_literal_removal,[],[f986])).

fof(f986,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_45 ),
    inference(resolution,[],[f934,f127])).

fof(f934,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_45 ),
    inference(avatar_component_clause,[],[f932])).

fof(f932,plain,
    ( spl7_45
  <=> v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f943,plain,
    ( ~ spl7_44
    | ~ spl7_45
    | ~ spl7_46
    | spl7_47
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f926,f643,f940,f936,f932,f928])).

fof(f926,plain,
    ( sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3)
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f925,f632])).

fof(f632,plain,(
    v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2)) ),
    inference(resolution,[],[f628,f214])).

fof(f628,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),X0)) ) ),
    inference(resolution,[],[f627,f214])).

fof(f627,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X3)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f626,f214])).

fof(f626,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f625,f215])).

fof(f625,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f624,f59])).

fof(f624,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X3)
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f623,f60])).

fof(f623,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X3)
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f622,f61])).

fof(f622,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f621])).

fof(f621,plain,(
    ! [X2,X3] :
      ( ~ l1_struct_0(X2)
      | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2))
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(sK2) ) ),
    inference(resolution,[],[f514,f127])).

fof(f514,plain,(
    ! [X19,X18] :
      ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3))
      | ~ l1_struct_0(X19)
      | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19))
      | ~ l1_struct_0(X18) ) ),
    inference(subsumption_resolution,[],[f513,f260])).

fof(f513,plain,(
    ! [X19,X18] :
      ( ~ l1_struct_0(X18)
      | ~ l1_struct_0(X19)
      | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X18)) ) ),
    inference(subsumption_resolution,[],[f486,f215])).

fof(f486,plain,(
    ! [X19,X18] :
      ( ~ l1_struct_0(X18)
      | ~ l1_struct_0(X19)
      | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X18))
      | ~ l1_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f481])).

fof(f481,plain,(
    ! [X19,X18] :
      ( ~ l1_struct_0(X18)
      | ~ l1_struct_0(X19)
      | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X18))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(X18) ) ),
    inference(resolution,[],[f264,f126])).

fof(f925,plain,
    ( sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2))
    | ~ sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3)
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f910,f214])).

fof(f910,plain,
    ( ~ l1_struct_0(sK2)
    | sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5)
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2))
    | ~ sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3)
    | ~ spl7_25 ),
    inference(resolution,[],[f902,f224])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0))))
      | sP0(X0,sK6,X1,sK2,sK5)
      | ~ v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0)
      | ~ v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0))
      | ~ v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2))
      | ~ sP1(sK5,sK2,X1,sK6,X0) ) ),
    inference(superposition,[],[f105,f66])).

fof(f105,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))))
      | sP0(X4,X3,X2,X1,X0)
      | ~ v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)
      | ~ v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4))
      | ~ v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))
      | ~ sP1(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f902,plain,
    ( ! [X2] :
        ( m1_subset_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ l1_struct_0(X2) )
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f899,f214])).

fof(f899,plain,
    ( ! [X2] :
        ( ~ l1_struct_0(X2)
        | m1_subset_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3))))
        | ~ l1_struct_0(sK2) )
    | ~ spl7_25 ),
    inference(resolution,[],[f516,f644])).

fof(f516,plain,(
    ! [X21,X20] :
      ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3))
      | ~ l1_struct_0(X21)
      | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3))))
      | ~ l1_struct_0(X20) ) ),
    inference(subsumption_resolution,[],[f515,f260])).

fof(f515,plain,(
    ! [X21,X20] :
      ( ~ l1_struct_0(X20)
      | ~ l1_struct_0(X21)
      | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3))))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X20)) ) ),
    inference(subsumption_resolution,[],[f485,f215])).

fof(f485,plain,(
    ! [X21,X20] :
      ( ~ l1_struct_0(X20)
      | ~ l1_struct_0(X21)
      | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3))))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X20))
      | ~ l1_struct_0(sK3) ) ),
    inference(duplicate_literal_removal,[],[f482])).

fof(f482,plain,(
    ! [X21,X20] :
      ( ~ l1_struct_0(X20)
      | ~ l1_struct_0(X21)
      | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3))))
      | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3))
      | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X20))
      | ~ l1_struct_0(sK3)
      | ~ l1_struct_0(X20) ) ),
    inference(resolution,[],[f264,f128])).

fof(f746,plain,(
    spl7_34 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | spl7_34 ),
    inference(subsumption_resolution,[],[f744,f55])).

fof(f744,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_34 ),
    inference(resolution,[],[f738,f102])).

fof(f102,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f738,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f736])).

fof(f736,plain,
    ( spl7_34
  <=> m1_pre_topc(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f743,plain,
    ( ~ spl7_34
    | spl7_35 ),
    inference(avatar_split_clause,[],[f734,f740,f736])).

fof(f734,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2) ),
    inference(subsumption_resolution,[],[f733,f54])).

fof(f733,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f732,f55])).

fof(f732,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f731,f56])).

fof(f731,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f730,f57])).

fof(f730,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f729,f58])).

fof(f729,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f728,f53])).

fof(f728,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f727,f59])).

fof(f727,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f726,f60])).

fof(f726,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f725,f61])).

fof(f725,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2) ),
    inference(duplicate_literal_removal,[],[f724])).

fof(f724,plain,
    ( r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_pre_topc(sK2,sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(superposition,[],[f120,f715])).

fof(f715,plain,(
    k2_tmap_1(sK2,sK3,sK4,sK2) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) ),
    inference(forward_demodulation,[],[f714,f522])).

fof(f522,plain,(
    k2_tmap_1(sK2,sK3,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f519,f55])).

fof(f519,plain,
    ( k2_tmap_1(sK2,sK3,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f256,f102])).

fof(f256,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f255,f53])).

fof(f255,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f254,f54])).

fof(f254,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f253,f55])).

fof(f253,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f252,f56])).

fof(f252,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f251,f57])).

fof(f251,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f250,f58])).

fof(f250,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f249,f59])).

fof(f249,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f227,f60])).

fof(f227,plain,(
    ! [X4] :
      ( ~ m1_pre_topc(X4,sK2)
      | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X0)
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
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
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f714,plain,(
    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) ),
    inference(subsumption_resolution,[],[f711,f55])).

fof(f711,plain,
    ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f698,f102])).

fof(f698,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4) ) ),
    inference(subsumption_resolution,[],[f697,f53])).

fof(f697,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f696,f54])).

fof(f696,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f695,f55])).

fof(f695,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2) ) ),
    inference(duplicate_literal_removal,[],[f694])).

fof(f694,plain,(
    ! [X0] :
      ( k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4)
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK2) ) ),
    inference(resolution,[],[f240,f102])).

fof(f240,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK2,X1)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,sK2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f239,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X1)
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f238,f56])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f237,f57])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f236,f58])).

fof(f236,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f235,f59])).

fof(f235,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f225,f60])).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,sK2)
      | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0))
      | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      | ~ v1_funct_1(sK4)
      | ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(sK2,X1)
      | ~ l1_pre_topc(sK3)
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f61,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ m1_pre_topc(X3,X2)
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
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
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).

fof(f692,plain,(
    spl7_25 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl7_25 ),
    inference(subsumption_resolution,[],[f690,f215])).

fof(f690,plain,
    ( ~ l1_struct_0(sK3)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f689,f59])).

fof(f689,plain,
    ( ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f688,f60])).

fof(f688,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f687,f61])).

fof(f687,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_25 ),
    inference(subsumption_resolution,[],[f686,f214])).

fof(f686,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | spl7_25 ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( ~ l1_struct_0(sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | spl7_25 ),
    inference(resolution,[],[f645,f127])).

fof(f645,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f643])).

fof(f203,plain,
    ( spl7_3
    | spl7_7 ),
    inference(avatar_split_clause,[],[f78,f158,f142])).

fof(f78,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f187,plain,
    ( spl7_3
    | spl7_11 ),
    inference(avatar_split_clause,[],[f94,f174,f142])).

fof(f94,plain,
    ( v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f181,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f100,f178,f174,f170,f166,f162,f158,f154,f150,f146,f142,f138,f134])).

fof(f100,plain,
    ( ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))
    | ~ m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)
    | ~ v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:04:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (8927)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (8919)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (8911)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (8905)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (8907)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (8909)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (8915)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (8925)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (8908)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (8918)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (8917)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (8926)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (8904)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (8922)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (8913)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (8910)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (8912)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (8916)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (8910)Refutation not found, incomplete strategy% (8910)------------------------------
% 0.21/0.54  % (8910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8910)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8910)Memory used [KB]: 10746
% 0.21/0.54  % (8910)Time elapsed: 0.136 s
% 0.21/0.54  % (8910)------------------------------
% 0.21/0.54  % (8910)------------------------------
% 0.21/0.54  % (8929)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (8924)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (8923)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (8906)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.55  % (8920)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (8928)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  % (8904)Refutation not found, incomplete strategy% (8904)------------------------------
% 0.21/0.56  % (8904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8904)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8904)Memory used [KB]: 10874
% 0.21/0.56  % (8904)Time elapsed: 0.125 s
% 0.21/0.56  % (8904)------------------------------
% 0.21/0.56  % (8904)------------------------------
% 0.21/0.56  % (8921)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (8914)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.57/0.57  % (8905)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.58  fof(f1648,plain,(
% 1.57/0.58    $false),
% 1.57/0.58    inference(avatar_sat_refutation,[],[f181,f187,f203,f692,f743,f746,f943,f994,f1318,f1346,f1373,f1375,f1377,f1498,f1509,f1513,f1573,f1604,f1625,f1634,f1636,f1639,f1647])).
% 1.57/0.58  fof(f1647,plain,(
% 1.57/0.58    spl7_10),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f1646])).
% 1.57/0.58  fof(f1646,plain,(
% 1.57/0.58    $false | spl7_10),
% 1.57/0.58    inference(subsumption_resolution,[],[f1645,f214])).
% 1.57/0.58  fof(f214,plain,(
% 1.57/0.58    l1_struct_0(sK2)),
% 1.57/0.58    inference(resolution,[],[f55,f101])).
% 1.57/0.58  fof(f101,plain,(
% 1.57/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f16])).
% 1.57/0.58  fof(f16,plain,(
% 1.57/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.57/0.58    inference(ennf_transformation,[],[f2])).
% 1.57/0.58  fof(f2,axiom,(
% 1.57/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.57/0.58  fof(f55,plain,(
% 1.57/0.58    l1_pre_topc(sK2)),
% 1.57/0.58    inference(cnf_transformation,[],[f45])).
% 1.57/0.58  fof(f45,plain,(
% 1.57/0.58    (((((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f39,f44,f43,f42,f41,f40])).
% 1.57/0.58  fof(f40,plain,(
% 1.57/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.78/0.59  fof(f41,plain,(
% 1.78/0.59    ? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(sK2,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) | ~v5_pre_topc(X2,sK2,X1) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(sK2,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(sK2,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(sK2,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v5_pre_topc(X2,sK2,X1) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.78/0.59    introduced(choice_axiom,[])).
% 1.78/0.59  fof(f42,plain,(
% 1.78/0.59    ? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(X2,sK2,sK3) | ~v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,X2,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,X2,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(X2,sK2,sK3) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(X2)) => (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))),
% 1.78/0.59    introduced(choice_axiom,[])).
% 1.78/0.59  fof(f43,plain,(
% 1.78/0.59    ? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X3),X3,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X3),u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X3))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,X3,X4) & sK2 = k1_tsep_1(sK2,X3,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,X4) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 1.78/0.59    introduced(choice_axiom,[])).
% 1.78/0.59  fof(f44,plain,(
% 1.78/0.59    ? [X4] : ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X4),X4,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X4),u1_struct_0(X4),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X4)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,X4) & sK2 = k1_tsep_1(sK2,sK5,X4) & m1_pre_topc(X4,sK2) & ~v2_struct_0(X4)) => ((~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)) & ((m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) & m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) & v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) | (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v5_pre_topc(sK4,sK2,sK3) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4))) & r4_tsep_1(sK2,sK5,sK6) & sK2 = k1_tsep_1(sK2,sK5,sK6) & m1_pre_topc(sK6,sK2) & ~v2_struct_0(sK6))),
% 1.78/0.59    introduced(choice_axiom,[])).
% 1.78/0.59  fof(f39,plain,(
% 1.78/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.59    inference(flattening,[],[f38])).
% 1.78/0.59  fof(f38,plain,(
% 1.78/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) | ~m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.59    inference(nnf_transformation,[],[f15])).
% 1.78/0.59  fof(f15,plain,(
% 1.78/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0 & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.59    inference(flattening,[],[f14])).
% 1.78/0.59  fof(f14,plain,(
% 1.78/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <~> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)))) & (r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0)) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f13])).
% 1.78/0.59  fof(f13,negated_conjecture,(
% 1.78/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.78/0.59    inference(negated_conjecture,[],[f12])).
% 1.78/0.59  fof(f12,conjecture,(
% 1.78/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((r4_tsep_1(X0,X3,X4) & k1_tsep_1(X0,X3,X4) = X0) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) <=> (m1_subset_1(k2_tmap_1(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X4),X4,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X4),u1_struct_0(X4),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X4)) & m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))))))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_tmap_1)).
% 1.78/0.59  fof(f1645,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | spl7_10),
% 1.78/0.59    inference(subsumption_resolution,[],[f1644,f215])).
% 1.78/0.59  fof(f215,plain,(
% 1.78/0.59    l1_struct_0(sK3)),
% 1.78/0.59    inference(resolution,[],[f58,f101])).
% 1.78/0.59  fof(f58,plain,(
% 1.78/0.59    l1_pre_topc(sK3)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1644,plain,(
% 1.78/0.59    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_10),
% 1.78/0.59    inference(subsumption_resolution,[],[f1643,f59])).
% 1.78/0.59  fof(f59,plain,(
% 1.78/0.59    v1_funct_1(sK4)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1643,plain,(
% 1.78/0.59    ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_10),
% 1.78/0.59    inference(subsumption_resolution,[],[f1642,f60])).
% 1.78/0.59  fof(f60,plain,(
% 1.78/0.59    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1642,plain,(
% 1.78/0.59    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_10),
% 1.78/0.59    inference(subsumption_resolution,[],[f1641,f61])).
% 1.78/0.59  fof(f61,plain,(
% 1.78/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1641,plain,(
% 1.78/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_10),
% 1.78/0.59    inference(subsumption_resolution,[],[f1640,f223])).
% 1.78/0.59  fof(f223,plain,(
% 1.78/0.59    l1_struct_0(sK6)),
% 1.78/0.59    inference(resolution,[],[f222,f101])).
% 1.78/0.59  fof(f222,plain,(
% 1.78/0.59    l1_pre_topc(sK6)),
% 1.78/0.59    inference(subsumption_resolution,[],[f221,f55])).
% 1.78/0.59  fof(f221,plain,(
% 1.78/0.59    l1_pre_topc(sK6) | ~l1_pre_topc(sK2)),
% 1.78/0.59    inference(resolution,[],[f65,f103])).
% 1.78/0.59  fof(f103,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f18])).
% 1.78/0.59  fof(f18,plain,(
% 1.78/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.78/0.59    inference(ennf_transformation,[],[f3])).
% 1.78/0.59  fof(f3,axiom,(
% 1.78/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.78/0.59  fof(f65,plain,(
% 1.78/0.59    m1_pre_topc(sK6,sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1640,plain,(
% 1.78/0.59    ~l1_struct_0(sK6) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_10),
% 1.78/0.59    inference(resolution,[],[f172,f127])).
% 1.78/0.59  fof(f127,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f32])).
% 1.78/0.59  fof(f32,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.78/0.59    inference(flattening,[],[f31])).
% 1.78/0.59  fof(f31,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f6])).
% 1.78/0.59  fof(f6,axiom,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tmap_1)).
% 1.78/0.59  fof(f172,plain,(
% 1.78/0.59    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | spl7_10),
% 1.78/0.59    inference(avatar_component_clause,[],[f170])).
% 1.78/0.59  fof(f170,plain,(
% 1.78/0.59    spl7_10 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.78/0.59  fof(f1639,plain,(
% 1.78/0.59    spl7_8),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1638])).
% 1.78/0.59  fof(f1638,plain,(
% 1.78/0.59    $false | spl7_8),
% 1.78/0.59    inference(subsumption_resolution,[],[f1637,f219])).
% 1.78/0.59  fof(f219,plain,(
% 1.78/0.59    l1_struct_0(sK5)),
% 1.78/0.59    inference(resolution,[],[f218,f101])).
% 1.78/0.59  fof(f218,plain,(
% 1.78/0.59    l1_pre_topc(sK5)),
% 1.78/0.59    inference(subsumption_resolution,[],[f217,f55])).
% 1.78/0.59  fof(f217,plain,(
% 1.78/0.59    l1_pre_topc(sK5) | ~l1_pre_topc(sK2)),
% 1.78/0.59    inference(resolution,[],[f63,f103])).
% 1.78/0.59  fof(f63,plain,(
% 1.78/0.59    m1_pre_topc(sK5,sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1637,plain,(
% 1.78/0.59    ~l1_struct_0(sK5) | spl7_8),
% 1.78/0.59    inference(resolution,[],[f164,f264])).
% 1.78/0.59  fof(f264,plain,(
% 1.78/0.59    ( ! [X9] : (m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3)))) | ~l1_struct_0(X9)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f263,f214])).
% 1.78/0.59  fof(f263,plain,(
% 1.78/0.59    ( ! [X9] : (~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3)))) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f262,f215])).
% 1.78/0.59  fof(f262,plain,(
% 1.78/0.59    ( ! [X9] : (~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3)))) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f261,f59])).
% 1.78/0.59  fof(f261,plain,(
% 1.78/0.59    ( ! [X9] : (~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3)))) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f232,f60])).
% 1.78/0.59  fof(f232,plain,(
% 1.78/0.59    ( ! [X9] : (~l1_struct_0(X9) | m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X9),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(resolution,[],[f61,f128])).
% 1.78/0.59  fof(f128,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f32])).
% 1.78/0.59  fof(f164,plain,(
% 1.78/0.59    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | spl7_8),
% 1.78/0.59    inference(avatar_component_clause,[],[f162])).
% 1.78/0.59  fof(f162,plain,(
% 1.78/0.59    spl7_8 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.78/0.59  fof(f1636,plain,(
% 1.78/0.59    spl7_9),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1635])).
% 1.78/0.59  fof(f1635,plain,(
% 1.78/0.59    $false | spl7_9),
% 1.78/0.59    inference(subsumption_resolution,[],[f272,f168])).
% 1.78/0.59  fof(f168,plain,(
% 1.78/0.59    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | spl7_9),
% 1.78/0.59    inference(avatar_component_clause,[],[f166])).
% 1.78/0.59  fof(f166,plain,(
% 1.78/0.59    spl7_9 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.78/0.59  fof(f272,plain,(
% 1.78/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6))),
% 1.78/0.59    inference(resolution,[],[f260,f223])).
% 1.78/0.59  fof(f260,plain,(
% 1.78/0.59    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8))) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f259,f214])).
% 1.78/0.59  fof(f259,plain,(
% 1.78/0.59    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8)) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f258,f215])).
% 1.78/0.59  fof(f258,plain,(
% 1.78/0.59    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f257,f59])).
% 1.78/0.59  fof(f257,plain,(
% 1.78/0.59    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f231,f60])).
% 1.78/0.59  fof(f231,plain,(
% 1.78/0.59    ( ! [X8] : (~l1_struct_0(X8) | v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X8)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(resolution,[],[f61,f126])).
% 1.78/0.59  fof(f126,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f32])).
% 1.78/0.59  fof(f1634,plain,(
% 1.78/0.59    spl7_12),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1633])).
% 1.78/0.59  fof(f1633,plain,(
% 1.78/0.59    $false | spl7_12),
% 1.78/0.59    inference(subsumption_resolution,[],[f1632,f223])).
% 1.78/0.59  fof(f1632,plain,(
% 1.78/0.59    ~l1_struct_0(sK6) | spl7_12),
% 1.78/0.59    inference(resolution,[],[f180,f264])).
% 1.78/0.59  fof(f180,plain,(
% 1.78/0.59    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | spl7_12),
% 1.78/0.59    inference(avatar_component_clause,[],[f178])).
% 1.78/0.59  fof(f178,plain,(
% 1.78/0.59    spl7_12 <=> m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3))))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.78/0.59  fof(f1625,plain,(
% 1.78/0.59    spl7_6),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1624])).
% 1.78/0.59  fof(f1624,plain,(
% 1.78/0.59    $false | spl7_6),
% 1.78/0.59    inference(subsumption_resolution,[],[f1623,f214])).
% 1.78/0.59  fof(f1623,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | spl7_6),
% 1.78/0.59    inference(subsumption_resolution,[],[f1622,f215])).
% 1.78/0.59  fof(f1622,plain,(
% 1.78/0.59    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_6),
% 1.78/0.59    inference(subsumption_resolution,[],[f1621,f59])).
% 1.78/0.59  fof(f1621,plain,(
% 1.78/0.59    ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_6),
% 1.78/0.59    inference(subsumption_resolution,[],[f1620,f60])).
% 1.78/0.59  fof(f1620,plain,(
% 1.78/0.59    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_6),
% 1.78/0.59    inference(subsumption_resolution,[],[f1619,f61])).
% 1.78/0.59  fof(f1619,plain,(
% 1.78/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_6),
% 1.78/0.59    inference(subsumption_resolution,[],[f1618,f219])).
% 1.78/0.59  fof(f1618,plain,(
% 1.78/0.59    ~l1_struct_0(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_6),
% 1.78/0.59    inference(resolution,[],[f156,f127])).
% 1.78/0.59  fof(f156,plain,(
% 1.78/0.59    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | spl7_6),
% 1.78/0.59    inference(avatar_component_clause,[],[f154])).
% 1.78/0.59  fof(f154,plain,(
% 1.78/0.59    spl7_6 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.78/0.59  fof(f1604,plain,(
% 1.78/0.59    spl7_11 | ~spl7_59),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1603])).
% 1.78/0.59  fof(f1603,plain,(
% 1.78/0.59    $false | (spl7_11 | ~spl7_59)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1602,f64])).
% 1.78/0.59  fof(f64,plain,(
% 1.78/0.59    ~v2_struct_0(sK6)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1602,plain,(
% 1.78/0.59    v2_struct_0(sK6) | (spl7_11 | ~spl7_59)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1600,f65])).
% 1.78/0.59  fof(f1600,plain,(
% 1.78/0.59    ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | (spl7_11 | ~spl7_59)),
% 1.78/0.59    inference(resolution,[],[f1345,f176])).
% 1.78/0.59  fof(f176,plain,(
% 1.78/0.59    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | spl7_11),
% 1.78/0.59    inference(avatar_component_clause,[],[f174])).
% 1.78/0.59  fof(f174,plain,(
% 1.78/0.59    spl7_11 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.78/0.59  fof(f1345,plain,(
% 1.78/0.59    ( ! [X7] : (v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~m1_pre_topc(X7,sK2) | v2_struct_0(X7)) ) | ~spl7_59),
% 1.78/0.59    inference(avatar_component_clause,[],[f1344])).
% 1.78/0.59  fof(f1344,plain,(
% 1.78/0.59    spl7_59 <=> ! [X7] : (~m1_pre_topc(X7,sK2) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | v2_struct_0(X7))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).
% 1.78/0.59  fof(f1573,plain,(
% 1.78/0.59    spl7_7 | ~spl7_25 | ~spl7_35 | ~spl7_47),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1572])).
% 1.78/0.59  fof(f1572,plain,(
% 1.78/0.59    $false | (spl7_7 | ~spl7_25 | ~spl7_35 | ~spl7_47)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1538,f160])).
% 1.78/0.59  fof(f160,plain,(
% 1.78/0.59    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | spl7_7),
% 1.78/0.59    inference(avatar_component_clause,[],[f158])).
% 1.78/0.59  fof(f158,plain,(
% 1.78/0.59    spl7_7 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.78/0.59  fof(f1538,plain,(
% 1.78/0.59    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | (~spl7_25 | ~spl7_35 | ~spl7_47)),
% 1.78/0.59    inference(resolution,[],[f1515,f112])).
% 1.78/0.59  fof(f112,plain,(
% 1.78/0.59    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f51])).
% 1.78/0.59  fof(f51,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) & ((m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) & m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) & v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) & v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) & v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 1.78/0.59    inference(rectify,[],[f50])).
% 1.78/0.59  fof(f50,plain,(
% 1.78/0.59    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.78/0.59    inference(flattening,[],[f49])).
% 1.78/0.59  fof(f49,plain,(
% 1.78/0.59    ! [X1,X3,X4,X0,X2] : ((sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) & ((m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))) | ~sP0(X1,X3,X4,X0,X2)))),
% 1.78/0.59    inference(nnf_transformation,[],[f35])).
% 1.78/0.59  fof(f35,plain,(
% 1.78/0.59    ! [X1,X3,X4,X0,X2] : (sP0(X1,X3,X4,X0,X2) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))),
% 1.78/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.78/0.59  fof(f1515,plain,(
% 1.78/0.59    sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_25 | ~spl7_35 | ~spl7_47)),
% 1.78/0.59    inference(forward_demodulation,[],[f942,f1273])).
% 1.78/0.59  fof(f1273,plain,(
% 1.78/0.59    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) | (~spl7_25 | ~spl7_35)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1272,f59])).
% 1.78/0.59  fof(f1272,plain,(
% 1.78/0.59    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) | ~v1_funct_1(sK4) | (~spl7_25 | ~spl7_35)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1271,f60])).
% 1.78/0.59  fof(f1271,plain,(
% 1.78/0.59    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | (~spl7_25 | ~spl7_35)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1270,f61])).
% 1.78/0.59  fof(f1270,plain,(
% 1.78/0.59    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | (~spl7_25 | ~spl7_35)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1269,f644])).
% 1.78/0.59  fof(f644,plain,(
% 1.78/0.59    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl7_25),
% 1.78/0.59    inference(avatar_component_clause,[],[f643])).
% 1.78/0.59  fof(f643,plain,(
% 1.78/0.59    spl7_25 <=> v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.78/0.59  fof(f1269,plain,(
% 1.78/0.59    sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl7_35),
% 1.78/0.59    inference(subsumption_resolution,[],[f1260,f214])).
% 1.78/0.59  fof(f1260,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | sK4 = k2_tmap_1(sK2,sK3,sK4,sK2) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~spl7_35),
% 1.78/0.59    inference(resolution,[],[f517,f742])).
% 1.78/0.59  fof(f742,plain,(
% 1.78/0.59    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~spl7_35),
% 1.78/0.59    inference(avatar_component_clause,[],[f740])).
% 1.78/0.59  fof(f740,plain,(
% 1.78/0.59    spl7_35 <=> r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.78/0.59  fof(f517,plain,(
% 1.78/0.59    ( ! [X23,X22] : (~r2_funct_2(u1_struct_0(X22),u1_struct_0(sK3),X23,k2_tmap_1(sK2,sK3,sK4,X22)) | ~l1_struct_0(X22) | k2_tmap_1(sK2,sK3,sK4,X22) = X23 | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X22),u1_struct_0(X22),u1_struct_0(sK3)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(sK3)))) | ~v1_funct_2(X23,u1_struct_0(X22),u1_struct_0(sK3)) | ~v1_funct_1(X23)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f483,f260])).
% 1.78/0.59  fof(f483,plain,(
% 1.78/0.59    ( ! [X23,X22] : (~l1_struct_0(X22) | ~r2_funct_2(u1_struct_0(X22),u1_struct_0(sK3),X23,k2_tmap_1(sK2,sK3,sK4,X22)) | k2_tmap_1(sK2,sK3,sK4,X22) = X23 | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X22),u1_struct_0(X22),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X22)) | ~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(sK3)))) | ~v1_funct_2(X23,u1_struct_0(X22),u1_struct_0(sK3)) | ~v1_funct_1(X23)) )),
% 1.78/0.59    inference(resolution,[],[f264,f129])).
% 1.78/0.59  fof(f129,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_funct_2(X0,X1,X2,X3) | X2 = X3 | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f52])).
% 1.78/0.59  fof(f52,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.78/0.59    inference(nnf_transformation,[],[f34])).
% 1.78/0.59  fof(f34,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.78/0.59    inference(flattening,[],[f33])).
% 1.78/0.59  fof(f33,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.78/0.59    inference(ennf_transformation,[],[f1])).
% 1.78/0.59  fof(f1,axiom,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.78/0.59  fof(f942,plain,(
% 1.78/0.59    sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) | ~spl7_47),
% 1.78/0.59    inference(avatar_component_clause,[],[f940])).
% 1.78/0.59  fof(f940,plain,(
% 1.78/0.59    spl7_47 <=> sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 1.78/0.59  fof(f1513,plain,(
% 1.78/0.59    ~spl7_3 | ~spl7_25 | ~spl7_35 | spl7_46),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1512])).
% 1.78/0.59  fof(f1512,plain,(
% 1.78/0.59    $false | (~spl7_3 | ~spl7_25 | ~spl7_35 | spl7_46)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1511,f143])).
% 1.78/0.59  fof(f143,plain,(
% 1.78/0.59    v5_pre_topc(sK4,sK2,sK3) | ~spl7_3),
% 1.78/0.59    inference(avatar_component_clause,[],[f142])).
% 1.78/0.59  fof(f142,plain,(
% 1.78/0.59    spl7_3 <=> v5_pre_topc(sK4,sK2,sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.78/0.59  fof(f1511,plain,(
% 1.78/0.59    ~v5_pre_topc(sK4,sK2,sK3) | (~spl7_25 | ~spl7_35 | spl7_46)),
% 1.78/0.59    inference(forward_demodulation,[],[f1510,f1273])).
% 1.78/0.59  fof(f1510,plain,(
% 1.78/0.59    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) | (~spl7_25 | ~spl7_35 | spl7_46)),
% 1.78/0.59    inference(forward_demodulation,[],[f938,f1273])).
% 1.78/0.59  fof(f938,plain,(
% 1.78/0.59    ~v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3) | spl7_46),
% 1.78/0.59    inference(avatar_component_clause,[],[f936])).
% 1.78/0.59  fof(f936,plain,(
% 1.78/0.59    spl7_46 <=> v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 1.78/0.59  fof(f1509,plain,(
% 1.78/0.59    ~spl7_25 | ~spl7_35 | spl7_44),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1508])).
% 1.78/0.59  fof(f1508,plain,(
% 1.78/0.59    $false | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1507,f62])).
% 1.78/0.59  fof(f62,plain,(
% 1.78/0.59    ~v2_struct_0(sK5)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1507,plain,(
% 1.78/0.59    v2_struct_0(sK5) | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1506,f63])).
% 1.78/0.59  fof(f1506,plain,(
% 1.78/0.59    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1505,f64])).
% 1.78/0.59  fof(f1505,plain,(
% 1.78/0.59    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1504,f65])).
% 1.78/0.59  fof(f1504,plain,(
% 1.78/0.59    ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1503,f67])).
% 1.78/0.59  fof(f67,plain,(
% 1.78/0.59    r4_tsep_1(sK2,sK5,sK6)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1503,plain,(
% 1.78/0.59    ~r4_tsep_1(sK2,sK5,sK6) | ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(resolution,[],[f1286,f248])).
% 1.78/0.59  fof(f248,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f247,f53])).
% 1.78/0.59  fof(f53,plain,(
% 1.78/0.59    ~v2_struct_0(sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f247,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f246,f54])).
% 1.78/0.59  fof(f54,plain,(
% 1.78/0.59    v2_pre_topc(sK2)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f246,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f245,f55])).
% 1.78/0.59  fof(f245,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f244,f56])).
% 1.78/0.59  fof(f56,plain,(
% 1.78/0.59    ~v2_struct_0(sK3)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f244,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f243,f57])).
% 1.78/0.59  fof(f57,plain,(
% 1.78/0.59    v2_pre_topc(sK3)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f243,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f242,f58])).
% 1.78/0.59  fof(f242,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f241,f59])).
% 1.78/0.59  fof(f241,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~v1_funct_1(sK4) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f226,f60])).
% 1.78/0.59  fof(f226,plain,(
% 1.78/0.59    ( ! [X2,X3] : (sP1(X2,sK2,sK4,X3,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~r4_tsep_1(sK2,X2,X3) | ~m1_pre_topc(X3,sK2) | v2_struct_0(X3) | ~m1_pre_topc(X2,sK2) | v2_struct_0(X2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(resolution,[],[f61,f119])).
% 1.78/0.59  fof(f119,plain,(
% 1.78/0.59    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | sP1(X2,X0,X4,X3,X1) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f37])).
% 1.78/0.59  fof(f37,plain,(
% 1.78/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (sP1(X2,X0,X4,X3,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.59    inference(definition_folding,[],[f22,f36,f35])).
% 1.78/0.59  fof(f36,plain,(
% 1.78/0.59    ! [X2,X0,X4,X3,X1] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> sP0(X1,X3,X4,X0,X2)) | ~sP1(X2,X0,X4,X3,X1))),
% 1.78/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.78/0.59  fof(f22,plain,(
% 1.78/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~r4_tsep_1(X0,X2,X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.59    inference(flattening,[],[f21])).
% 1.78/0.59  fof(f21,plain,(
% 1.78/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((! [X4] : (((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~r4_tsep_1(X0,X2,X3)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f8])).
% 1.78/0.59  fof(f8,axiom,(
% 1.78/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (r4_tsep_1(X0,X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => ((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) <=> (m1_subset_1(k2_tmap_1(X0,X1,X4,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X3)) & m1_subset_1(k2_tmap_1(X0,X1,X4,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,X2),X2,X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,X2),u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,X2))))))))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_tmap_1)).
% 1.78/0.59  fof(f1286,plain,(
% 1.78/0.59    ~sP1(sK5,sK2,sK4,sK6,sK3) | (~spl7_25 | ~spl7_35 | spl7_44)),
% 1.78/0.59    inference(backward_demodulation,[],[f930,f1273])).
% 1.78/0.59  fof(f930,plain,(
% 1.78/0.59    ~sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3) | spl7_44),
% 1.78/0.59    inference(avatar_component_clause,[],[f928])).
% 1.78/0.59  fof(f928,plain,(
% 1.78/0.59    spl7_44 <=> sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 1.78/0.59  fof(f1498,plain,(
% 1.78/0.59    spl7_5),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1497])).
% 1.78/0.59  fof(f1497,plain,(
% 1.78/0.59    $false | spl7_5),
% 1.78/0.59    inference(subsumption_resolution,[],[f271,f152])).
% 1.78/0.59  fof(f152,plain,(
% 1.78/0.59    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | spl7_5),
% 1.78/0.59    inference(avatar_component_clause,[],[f150])).
% 1.78/0.59  fof(f150,plain,(
% 1.78/0.59    spl7_5 <=> v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.78/0.59  fof(f271,plain,(
% 1.78/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))),
% 1.78/0.59    inference(resolution,[],[f260,f219])).
% 1.78/0.59  fof(f1377,plain,(
% 1.78/0.59    spl7_2),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1376])).
% 1.78/0.59  fof(f1376,plain,(
% 1.78/0.59    $false | spl7_2),
% 1.78/0.59    inference(subsumption_resolution,[],[f140,f60])).
% 1.78/0.59  fof(f140,plain,(
% 1.78/0.59    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_2),
% 1.78/0.59    inference(avatar_component_clause,[],[f138])).
% 1.78/0.59  fof(f138,plain,(
% 1.78/0.59    spl7_2 <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.78/0.59  fof(f1375,plain,(
% 1.78/0.59    spl7_4),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1374])).
% 1.78/0.59  fof(f1374,plain,(
% 1.78/0.59    $false | spl7_4),
% 1.78/0.59    inference(subsumption_resolution,[],[f148,f61])).
% 1.78/0.59  fof(f148,plain,(
% 1.78/0.59    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | spl7_4),
% 1.78/0.59    inference(avatar_component_clause,[],[f146])).
% 1.78/0.59  fof(f146,plain,(
% 1.78/0.59    spl7_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.78/0.59  fof(f1373,plain,(
% 1.78/0.59    spl7_1),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1372])).
% 1.78/0.59  fof(f1372,plain,(
% 1.78/0.59    $false | spl7_1),
% 1.78/0.59    inference(subsumption_resolution,[],[f136,f59])).
% 1.78/0.59  fof(f136,plain,(
% 1.78/0.59    ~v1_funct_1(sK4) | spl7_1),
% 1.78/0.59    inference(avatar_component_clause,[],[f134])).
% 1.78/0.59  fof(f134,plain,(
% 1.78/0.59    spl7_1 <=> v1_funct_1(sK4)),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.78/0.59  fof(f1346,plain,(
% 1.78/0.59    ~spl7_3 | spl7_59),
% 1.78/0.59    inference(avatar_split_clause,[],[f1342,f1344,f142])).
% 1.78/0.59  fof(f1342,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1341,f53])).
% 1.78/0.59  fof(f1341,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1340,f54])).
% 1.78/0.59  fof(f1340,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1339,f55])).
% 1.78/0.59  fof(f1339,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1338,f56])).
% 1.78/0.59  fof(f1338,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1337,f57])).
% 1.78/0.59  fof(f1337,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1336,f58])).
% 1.78/0.59  fof(f1336,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f1335,f59])).
% 1.78/0.59  fof(f1335,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f230,f60])).
% 1.78/0.59  fof(f230,plain,(
% 1.78/0.59    ( ! [X7] : (~m1_pre_topc(X7,sK2) | v2_struct_0(X7) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X7),X7,sK3) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.59    inference(resolution,[],[f61,f125])).
% 1.78/0.59  fof(f125,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f30])).
% 1.78/0.59  fof(f30,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.59    inference(flattening,[],[f29])).
% 1.78/0.59  fof(f29,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.59    inference(ennf_transformation,[],[f7])).
% 1.78/0.59  fof(f7,axiom,(
% 1.78/0.59    ! [X0,X1,X2,X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v5_pre_topc(X2,X0,X1) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 1.78/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).
% 1.78/0.59  fof(f1318,plain,(
% 1.78/0.59    spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_25 | ~spl7_35),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f1317])).
% 1.78/0.59  fof(f1317,plain,(
% 1.78/0.59    $false | (spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_25 | ~spl7_35)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1289,f144])).
% 1.78/0.59  fof(f144,plain,(
% 1.78/0.59    ~v5_pre_topc(sK4,sK2,sK3) | spl7_3),
% 1.78/0.59    inference(avatar_component_clause,[],[f142])).
% 1.78/0.59  fof(f1289,plain,(
% 1.78/0.59    v5_pre_topc(sK4,sK2,sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12 | ~spl7_25 | ~spl7_35)),
% 1.78/0.59    inference(backward_demodulation,[],[f1028,f1273])).
% 1.78/0.59  fof(f1028,plain,(
% 1.78/0.59    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(forward_demodulation,[],[f1027,f66])).
% 1.78/0.59  fof(f66,plain,(
% 1.78/0.59    sK2 = k1_tsep_1(sK2,sK5,sK6)),
% 1.78/0.59    inference(cnf_transformation,[],[f45])).
% 1.78/0.59  fof(f1027,plain,(
% 1.78/0.59    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1026,f67])).
% 1.78/0.59  fof(f1026,plain,(
% 1.78/0.59    ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1025,f62])).
% 1.78/0.59  fof(f1025,plain,(
% 1.78/0.59    v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1024,f63])).
% 1.78/0.59  fof(f1024,plain,(
% 1.78/0.59    ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1023,f64])).
% 1.78/0.59  fof(f1023,plain,(
% 1.78/0.59    v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1018,f65])).
% 1.78/0.59  fof(f1018,plain,(
% 1.78/0.59    ~m1_pre_topc(sK6,sK2) | v2_struct_0(sK6) | ~m1_pre_topc(sK5,sK2) | v2_struct_0(sK5) | ~r4_tsep_1(sK2,sK5,sK6) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,sK5,sK6)),k1_tsep_1(sK2,sK5,sK6),sK3) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(resolution,[],[f617,f763])).
% 1.78/0.59  fof(f763,plain,(
% 1.78/0.59    sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f762,f167])).
% 1.78/0.59  fof(f167,plain,(
% 1.78/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~spl7_9),
% 1.78/0.59    inference(avatar_component_clause,[],[f166])).
% 1.78/0.59  fof(f762,plain,(
% 1.78/0.59    ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_10 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f761,f171])).
% 1.78/0.59  fof(f171,plain,(
% 1.78/0.59    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~spl7_10),
% 1.78/0.59    inference(avatar_component_clause,[],[f170])).
% 1.78/0.59  fof(f761,plain,(
% 1.78/0.59    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_11 | ~spl7_12)),
% 1.78/0.59    inference(subsumption_resolution,[],[f756,f175])).
% 1.78/0.59  fof(f175,plain,(
% 1.78/0.59    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~spl7_11),
% 1.78/0.59    inference(avatar_component_clause,[],[f174])).
% 1.78/0.59  fof(f756,plain,(
% 1.78/0.59    ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | sP0(sK3,sK6,sK4,sK2,sK5) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_12)),
% 1.78/0.59    inference(resolution,[],[f288,f179])).
% 1.78/0.59  fof(f179,plain,(
% 1.78/0.59    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~spl7_12),
% 1.78/0.59    inference(avatar_component_clause,[],[f178])).
% 1.78/0.59  fof(f288,plain,(
% 1.78/0.59    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5)) ) | (~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.78/0.59    inference(subsumption_resolution,[],[f287,f151])).
% 1.78/0.59  fof(f151,plain,(
% 1.78/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~spl7_5),
% 1.78/0.59    inference(avatar_component_clause,[],[f150])).
% 1.78/0.59  fof(f287,plain,(
% 1.78/0.59    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | (~spl7_6 | ~spl7_7 | ~spl7_8)),
% 1.78/0.59    inference(subsumption_resolution,[],[f286,f155])).
% 1.78/0.59  fof(f155,plain,(
% 1.78/0.59    v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl7_6),
% 1.78/0.59    inference(avatar_component_clause,[],[f154])).
% 1.78/0.59  fof(f286,plain,(
% 1.78/0.59    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | (~spl7_7 | ~spl7_8)),
% 1.78/0.59    inference(subsumption_resolution,[],[f275,f159])).
% 1.78/0.59  fof(f159,plain,(
% 1.78/0.59    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~spl7_7),
% 1.78/0.59    inference(avatar_component_clause,[],[f158])).
% 1.78/0.59  fof(f275,plain,(
% 1.78/0.59    ( ! [X0] : (~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,X0),X0,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X0),u1_struct_0(X0),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X0)) | sP0(sK3,X0,sK4,sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5))) ) | ~spl7_8),
% 1.78/0.59    inference(resolution,[],[f163,f118])).
% 1.78/0.59  fof(f118,plain,(
% 1.78/0.59    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X3,X0,X2,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X0)))) | ~m1_subset_1(k2_tmap_1(X3,X0,X2,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X1),X1,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X1)) | sP0(X0,X1,X2,X3,X4) | ~v5_pre_topc(k2_tmap_1(X3,X0,X2,X4),X4,X0) | ~v1_funct_2(k2_tmap_1(X3,X0,X2,X4),u1_struct_0(X4),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(X3,X0,X2,X4))) )),
% 1.78/0.59    inference(cnf_transformation,[],[f51])).
% 1.78/0.59  fof(f163,plain,(
% 1.78/0.59    m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl7_8),
% 1.78/0.59    inference(avatar_component_clause,[],[f162])).
% 1.78/0.59  fof(f617,plain,(
% 1.78/0.59    ( ! [X4,X5] : (~sP0(sK3,X5,sK4,sK2,X4) | ~m1_pre_topc(X5,sK2) | v2_struct_0(X5) | ~m1_pre_topc(X4,sK2) | v2_struct_0(X4) | ~r4_tsep_1(sK2,X4,X5) | v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,k1_tsep_1(sK2,X4,X5)),k1_tsep_1(sK2,X4,X5),sK3)) )),
% 1.78/0.59    inference(resolution,[],[f248,f108])).
% 1.78/0.59  fof(f108,plain,(
% 1.78/0.59    ( ! [X4,X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3,X4) | ~sP0(X4,X3,X2,X1,X0) | v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f48])).
% 1.78/0.59  fof(f48,plain,(
% 1.78/0.59    ! [X0,X1,X2,X3,X4] : ((((m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) & v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) & v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) & v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)))) | ~sP0(X4,X3,X2,X1,X0)) & (sP0(X4,X3,X2,X1,X0) | ~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))))) | ~sP1(X0,X1,X2,X3,X4))),
% 1.78/0.59    inference(rectify,[],[f47])).
% 1.78/0.59  fof(f47,plain,(
% 1.78/0.59    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | ~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.78/0.59    inference(flattening,[],[f46])).
% 1.78/0.59  fof(f46,plain,(
% 1.78/0.59    ! [X2,X0,X4,X3,X1] : ((((m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) & v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))) | ~sP0(X1,X3,X4,X0,X2)) & (sP0(X1,X3,X4,X0,X2) | (~m1_subset_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v5_pre_topc(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),k1_tsep_1(X0,X2,X3),X1) | ~v1_funct_2(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(k2_tmap_1(X0,X1,X4,k1_tsep_1(X0,X2,X3)))))) | ~sP1(X2,X0,X4,X3,X1))),
% 1.78/0.59    inference(nnf_transformation,[],[f36])).
% 1.78/0.59  fof(f994,plain,(
% 1.78/0.59    ~spl7_25 | spl7_45),
% 1.78/0.59    inference(avatar_contradiction_clause,[],[f993])).
% 1.78/0.59  fof(f993,plain,(
% 1.78/0.59    $false | (~spl7_25 | spl7_45)),
% 1.78/0.59    inference(subsumption_resolution,[],[f992,f214])).
% 1.78/0.59  fof(f992,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | (~spl7_25 | spl7_45)),
% 1.78/0.59    inference(resolution,[],[f991,f264])).
% 1.78/0.59  fof(f991,plain,(
% 1.78/0.59    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | (~spl7_25 | spl7_45)),
% 1.78/0.59    inference(subsumption_resolution,[],[f990,f215])).
% 1.78/0.59  fof(f990,plain,(
% 1.78/0.59    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~l1_struct_0(sK3) | (~spl7_25 | spl7_45)),
% 1.78/0.59    inference(subsumption_resolution,[],[f989,f269])).
% 1.78/0.59  fof(f269,plain,(
% 1.78/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2))),
% 1.78/0.59    inference(resolution,[],[f260,f214])).
% 1.78/0.59  fof(f989,plain,(
% 1.78/0.59    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) | ~l1_struct_0(sK3) | (~spl7_25 | spl7_45)),
% 1.78/0.59    inference(subsumption_resolution,[],[f988,f644])).
% 1.78/0.59  fof(f988,plain,(
% 1.78/0.59    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) | ~l1_struct_0(sK3) | spl7_45),
% 1.78/0.59    inference(subsumption_resolution,[],[f987,f214])).
% 1.78/0.59  fof(f987,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) | ~l1_struct_0(sK3) | spl7_45),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f986])).
% 1.78/0.59  fof(f986,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK2)) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_45),
% 1.78/0.59    inference(resolution,[],[f934,f127])).
% 1.78/0.59  fof(f934,plain,(
% 1.78/0.59    ~v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_45),
% 1.78/0.59    inference(avatar_component_clause,[],[f932])).
% 1.78/0.59  fof(f932,plain,(
% 1.78/0.59    spl7_45 <=> v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3))),
% 1.78/0.59    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.78/0.59  fof(f943,plain,(
% 1.78/0.59    ~spl7_44 | ~spl7_45 | ~spl7_46 | spl7_47 | ~spl7_25),
% 1.78/0.59    inference(avatar_split_clause,[],[f926,f643,f940,f936,f932,f928])).
% 1.78/0.59  fof(f926,plain,(
% 1.78/0.59    sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3) | ~spl7_25),
% 1.78/0.59    inference(subsumption_resolution,[],[f925,f632])).
% 1.78/0.59  fof(f632,plain,(
% 1.78/0.59    v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2))),
% 1.78/0.59    inference(resolution,[],[f628,f214])).
% 1.78/0.59  fof(f628,plain,(
% 1.78/0.59    ( ! [X0] : (~l1_struct_0(X0) | v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),X0))) )),
% 1.78/0.59    inference(resolution,[],[f627,f214])).
% 1.78/0.59  fof(f627,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X3) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f626,f214])).
% 1.78/0.59  fof(f626,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X2) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f625,f215])).
% 1.78/0.59  fof(f625,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X2) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X3) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f624,f59])).
% 1.78/0.59  fof(f624,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X2) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X3) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f623,f60])).
% 1.78/0.59  fof(f623,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X2) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f622,f61])).
% 1.78/0.59  fof(f622,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X2) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f621])).
% 1.78/0.59  fof(f621,plain,(
% 1.78/0.59    ( ! [X2,X3] : (~l1_struct_0(X2) | v1_funct_1(k2_tmap_1(X3,sK3,k2_tmap_1(sK2,sK3,sK4,X3),X2)) | ~l1_struct_0(X3) | ~l1_struct_0(X3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)) )),
% 1.78/0.59    inference(resolution,[],[f514,f127])).
% 1.78/0.59  fof(f514,plain,(
% 1.78/0.59    ( ! [X19,X18] : (~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3)) | ~l1_struct_0(X19) | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19)) | ~l1_struct_0(X18)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f513,f260])).
% 1.78/0.59  fof(f513,plain,(
% 1.78/0.59    ( ! [X19,X18] : (~l1_struct_0(X18) | ~l1_struct_0(X19) | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19)) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X18))) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f486,f215])).
% 1.78/0.59  fof(f486,plain,(
% 1.78/0.59    ( ! [X19,X18] : (~l1_struct_0(X18) | ~l1_struct_0(X19) | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19)) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X18)) | ~l1_struct_0(sK3)) )),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f481])).
% 1.78/0.59  fof(f481,plain,(
% 1.78/0.59    ( ! [X19,X18] : (~l1_struct_0(X18) | ~l1_struct_0(X19) | v1_funct_1(k2_tmap_1(X18,sK3,k2_tmap_1(sK2,sK3,sK4,X18),X19)) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X18),u1_struct_0(X18),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X18)) | ~l1_struct_0(sK3) | ~l1_struct_0(X18)) )),
% 1.78/0.59    inference(resolution,[],[f264,f126])).
% 1.78/0.59  fof(f925,plain,(
% 1.78/0.59    sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2)) | ~sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3) | ~spl7_25),
% 1.78/0.59    inference(subsumption_resolution,[],[f910,f214])).
% 1.78/0.59  fof(f910,plain,(
% 1.78/0.59    ~l1_struct_0(sK2) | sP0(sK3,sK6,k2_tmap_1(sK2,sK3,sK4,sK2),sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),sK2,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),sK2)) | ~sP1(sK5,sK2,k2_tmap_1(sK2,sK3,sK4,sK2),sK6,sK3) | ~spl7_25),
% 1.78/0.59    inference(resolution,[],[f902,f224])).
% 1.78/0.59  fof(f224,plain,(
% 1.78/0.59    ( ! [X0,X1] : (~m1_subset_1(k2_tmap_1(sK2,X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0)))) | sP0(X0,sK6,X1,sK2,sK5) | ~v5_pre_topc(k2_tmap_1(sK2,X0,X1,sK2),sK2,X0) | ~v1_funct_2(k2_tmap_1(sK2,X0,X1,sK2),u1_struct_0(sK2),u1_struct_0(X0)) | ~v1_funct_1(k2_tmap_1(sK2,X0,X1,sK2)) | ~sP1(sK5,sK2,X1,sK6,X0)) )),
% 1.78/0.59    inference(superposition,[],[f105,f66])).
% 1.78/0.60  fof(f105,plain,(
% 1.78/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)))) | sP0(X4,X3,X2,X1,X0) | ~v5_pre_topc(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),k1_tsep_1(X1,X0,X3),X4) | ~v1_funct_2(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3)),u1_struct_0(k1_tsep_1(X1,X0,X3)),u1_struct_0(X4)) | ~v1_funct_1(k2_tmap_1(X1,X4,X2,k1_tsep_1(X1,X0,X3))) | ~sP1(X0,X1,X2,X3,X4)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f48])).
% 1.78/0.60  fof(f902,plain,(
% 1.78/0.60    ( ! [X2] : (m1_subset_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) | ~l1_struct_0(X2)) ) | ~spl7_25),
% 1.78/0.60    inference(subsumption_resolution,[],[f899,f214])).
% 1.78/0.60  fof(f899,plain,(
% 1.78/0.60    ( ! [X2] : (~l1_struct_0(X2) | m1_subset_1(k2_tmap_1(sK2,sK3,k2_tmap_1(sK2,sK3,sK4,sK2),X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK3)))) | ~l1_struct_0(sK2)) ) | ~spl7_25),
% 1.78/0.60    inference(resolution,[],[f516,f644])).
% 1.78/0.60  fof(f516,plain,(
% 1.78/0.60    ( ! [X21,X20] : (~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3)) | ~l1_struct_0(X21) | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3)))) | ~l1_struct_0(X20)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f515,f260])).
% 1.78/0.60  fof(f515,plain,(
% 1.78/0.60    ( ! [X21,X20] : (~l1_struct_0(X20) | ~l1_struct_0(X21) | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X20))) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f485,f215])).
% 1.78/0.60  fof(f485,plain,(
% 1.78/0.60    ( ! [X21,X20] : (~l1_struct_0(X20) | ~l1_struct_0(X21) | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X20)) | ~l1_struct_0(sK3)) )),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f482])).
% 1.78/0.60  fof(f482,plain,(
% 1.78/0.60    ( ! [X21,X20] : (~l1_struct_0(X20) | ~l1_struct_0(X21) | m1_subset_1(k2_tmap_1(X20,sK3,k2_tmap_1(sK2,sK3,sK4,X20),X21),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(sK3)))) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,X20),u1_struct_0(X20),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,X20)) | ~l1_struct_0(sK3) | ~l1_struct_0(X20)) )),
% 1.78/0.60    inference(resolution,[],[f264,f128])).
% 1.78/0.60  fof(f746,plain,(
% 1.78/0.60    spl7_34),
% 1.78/0.60    inference(avatar_contradiction_clause,[],[f745])).
% 1.78/0.60  fof(f745,plain,(
% 1.78/0.60    $false | spl7_34),
% 1.78/0.60    inference(subsumption_resolution,[],[f744,f55])).
% 1.78/0.60  fof(f744,plain,(
% 1.78/0.60    ~l1_pre_topc(sK2) | spl7_34),
% 1.78/0.60    inference(resolution,[],[f738,f102])).
% 1.78/0.60  fof(f102,plain,(
% 1.78/0.60    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f17])).
% 1.78/0.60  fof(f17,plain,(
% 1.78/0.60    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.78/0.60    inference(ennf_transformation,[],[f9])).
% 1.78/0.60  fof(f9,axiom,(
% 1.78/0.60    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.78/0.60  fof(f738,plain,(
% 1.78/0.60    ~m1_pre_topc(sK2,sK2) | spl7_34),
% 1.78/0.60    inference(avatar_component_clause,[],[f736])).
% 1.78/0.60  fof(f736,plain,(
% 1.78/0.60    spl7_34 <=> m1_pre_topc(sK2,sK2)),
% 1.78/0.60    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.78/0.60  fof(f743,plain,(
% 1.78/0.60    ~spl7_34 | spl7_35),
% 1.78/0.60    inference(avatar_split_clause,[],[f734,f740,f736])).
% 1.78/0.60  fof(f734,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f733,f54])).
% 1.78/0.60  fof(f733,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f732,f55])).
% 1.78/0.60  fof(f732,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f731,f56])).
% 1.78/0.60  fof(f731,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f730,f57])).
% 1.78/0.60  fof(f730,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f729,f58])).
% 1.78/0.60  fof(f729,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f728,f53])).
% 1.78/0.60  fof(f728,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f727,f59])).
% 1.78/0.60  fof(f727,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f726,f60])).
% 1.78/0.60  fof(f726,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(subsumption_resolution,[],[f725,f61])).
% 1.78/0.60  fof(f725,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2)),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f724])).
% 1.78/0.60  fof(f724,plain,(
% 1.78/0.60    r2_funct_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_tmap_1(sK2,sK3,sK4,sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(sK2,sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.78/0.60    inference(superposition,[],[f120,f715])).
% 1.78/0.60  fof(f715,plain,(
% 1.78/0.60    k2_tmap_1(sK2,sK3,sK4,sK2) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)),
% 1.78/0.60    inference(forward_demodulation,[],[f714,f522])).
% 1.78/0.60  fof(f522,plain,(
% 1.78/0.60    k2_tmap_1(sK2,sK3,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2))),
% 1.78/0.60    inference(subsumption_resolution,[],[f519,f55])).
% 1.78/0.60  fof(f519,plain,(
% 1.78/0.60    k2_tmap_1(sK2,sK3,sK4,sK2) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) | ~l1_pre_topc(sK2)),
% 1.78/0.60    inference(resolution,[],[f256,f102])).
% 1.78/0.60  fof(f256,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4))) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f255,f53])).
% 1.78/0.60  fof(f255,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f254,f54])).
% 1.78/0.60  fof(f254,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f253,f55])).
% 1.78/0.60  fof(f253,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f252,f56])).
% 1.78/0.60  fof(f252,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f251,f57])).
% 1.78/0.60  fof(f251,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f250,f58])).
% 1.78/0.60  fof(f250,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f249,f59])).
% 1.78/0.60  fof(f249,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f227,f60])).
% 1.78/0.60  fof(f227,plain,(
% 1.78/0.60    ( ! [X4] : (~m1_pre_topc(X4,sK2) | k2_tmap_1(sK2,sK3,sK4,X4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X4)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(resolution,[],[f61,f121])).
% 1.78/0.60  fof(f121,plain,(
% 1.78/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X0) | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f26])).
% 1.78/0.60  fof(f26,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.60    inference(flattening,[],[f25])).
% 1.78/0.60  fof(f25,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f4])).
% 1.78/0.60  fof(f4,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).
% 1.78/0.60  fof(f714,plain,(
% 1.78/0.60    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4)),
% 1.78/0.60    inference(subsumption_resolution,[],[f711,f55])).
% 1.78/0.60  fof(f711,plain,(
% 1.78/0.60    k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK2,sK3,sK2,sK2,sK4) | ~l1_pre_topc(sK2)),
% 1.78/0.60    inference(resolution,[],[f698,f102])).
% 1.78/0.60  fof(f698,plain,(
% 1.78/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK2) | k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f697,f53])).
% 1.78/0.60  fof(f697,plain,(
% 1.78/0.60    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4) | ~m1_pre_topc(X0,sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f696,f54])).
% 1.78/0.60  fof(f696,plain,(
% 1.78/0.60    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4) | ~m1_pre_topc(X0,sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f695,f55])).
% 1.78/0.60  fof(f695,plain,(
% 1.78/0.60    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) )),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f694])).
% 1.78/0.60  fof(f694,plain,(
% 1.78/0.60    ( ! [X0] : (k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) = k3_tmap_1(sK2,sK3,sK2,X0,sK4) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK2)) )),
% 1.78/0.60    inference(resolution,[],[f240,f102])).
% 1.78/0.60  fof(f240,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(sK2,X1) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,sK2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f239,f122])).
% 1.78/0.60  fof(f122,plain,(
% 1.78/0.60    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X1) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f28])).
% 1.78/0.60  fof(f28,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.78/0.60    inference(flattening,[],[f27])).
% 1.78/0.60  fof(f27,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f11])).
% 1.78/0.60  fof(f11,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tsep_1)).
% 1.78/0.60  fof(f239,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f238,f56])).
% 1.78/0.60  fof(f238,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f237,f57])).
% 1.78/0.60  fof(f237,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f236,f58])).
% 1.78/0.60  fof(f236,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f235,f59])).
% 1.78/0.60  fof(f235,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(subsumption_resolution,[],[f225,f60])).
% 1.78/0.60  fof(f225,plain,(
% 1.78/0.60    ( ! [X0,X1] : (~m1_pre_topc(X0,sK2) | k3_tmap_1(X1,sK3,sK2,X0,sK4) = k2_partfun1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(X0)) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~m1_pre_topc(X0,X1) | ~m1_pre_topc(sK2,X1) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 1.78/0.60    inference(resolution,[],[f61,f104])).
% 1.78/0.60  fof(f104,plain,(
% 1.78/0.60    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~m1_pre_topc(X3,X2) | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f20])).
% 1.78/0.60  fof(f20,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.60    inference(flattening,[],[f19])).
% 1.78/0.60  fof(f19,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f5])).
% 1.78/0.60  fof(f5,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).
% 1.78/0.60  fof(f120,plain,(
% 1.78/0.60    ( ! [X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.78/0.60    inference(cnf_transformation,[],[f24])).
% 1.78/0.60  fof(f24,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.60    inference(flattening,[],[f23])).
% 1.78/0.60  fof(f23,plain,(
% 1.78/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.60    inference(ennf_transformation,[],[f10])).
% 1.78/0.60  fof(f10,axiom,(
% 1.78/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),X3,k3_tmap_1(X0,X1,X2,X2,X3))))))),
% 1.78/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tmap_1)).
% 1.78/0.60  fof(f692,plain,(
% 1.78/0.60    spl7_25),
% 1.78/0.60    inference(avatar_contradiction_clause,[],[f691])).
% 1.78/0.60  fof(f691,plain,(
% 1.78/0.60    $false | spl7_25),
% 1.78/0.60    inference(subsumption_resolution,[],[f690,f215])).
% 1.78/0.60  fof(f690,plain,(
% 1.78/0.60    ~l1_struct_0(sK3) | spl7_25),
% 1.78/0.60    inference(subsumption_resolution,[],[f689,f59])).
% 1.78/0.60  fof(f689,plain,(
% 1.78/0.60    ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | spl7_25),
% 1.78/0.60    inference(subsumption_resolution,[],[f688,f60])).
% 1.78/0.60  fof(f688,plain,(
% 1.78/0.60    ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | spl7_25),
% 1.78/0.60    inference(subsumption_resolution,[],[f687,f61])).
% 1.78/0.60  fof(f687,plain,(
% 1.78/0.60    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | spl7_25),
% 1.78/0.60    inference(subsumption_resolution,[],[f686,f214])).
% 1.78/0.60  fof(f686,plain,(
% 1.78/0.60    ~l1_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | spl7_25),
% 1.78/0.60    inference(duplicate_literal_removal,[],[f685])).
% 1.78/0.60  fof(f685,plain,(
% 1.78/0.60    ~l1_struct_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | spl7_25),
% 1.78/0.60    inference(resolution,[],[f645,f127])).
% 1.78/0.60  fof(f645,plain,(
% 1.78/0.60    ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK3)) | spl7_25),
% 1.78/0.60    inference(avatar_component_clause,[],[f643])).
% 1.78/0.60  fof(f203,plain,(
% 1.78/0.60    spl7_3 | spl7_7),
% 1.78/0.60    inference(avatar_split_clause,[],[f78,f158,f142])).
% 1.78/0.60  fof(f78,plain,(
% 1.78/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 1.78/0.60    inference(cnf_transformation,[],[f45])).
% 1.78/0.60  fof(f187,plain,(
% 1.78/0.60    spl7_3 | spl7_11),
% 1.78/0.60    inference(avatar_split_clause,[],[f94,f174,f142])).
% 1.78/0.60  fof(f94,plain,(
% 1.78/0.60    v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | v5_pre_topc(sK4,sK2,sK3)),
% 1.78/0.60    inference(cnf_transformation,[],[f45])).
% 1.78/0.60  fof(f181,plain,(
% 1.78/0.60    ~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_8 | ~spl7_9 | ~spl7_10 | ~spl7_11 | ~spl7_12),
% 1.78/0.60    inference(avatar_split_clause,[],[f100,f178,f174,f170,f166,f162,f158,f154,f150,f146,f142,f138,f134])).
% 1.78/0.60  fof(f100,plain,(
% 1.78/0.60    ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK6),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK6),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK6),sK6,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK6),u1_struct_0(sK6),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK6)) | ~m1_subset_1(k2_tmap_1(sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v5_pre_topc(k2_tmap_1(sK2,sK3,sK4,sK5),sK5,sK3) | ~v1_funct_2(k2_tmap_1(sK2,sK3,sK4,sK5),u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(k2_tmap_1(sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) | ~v5_pre_topc(sK4,sK2,sK3) | ~v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) | ~v1_funct_1(sK4)),
% 1.78/0.60    inference(cnf_transformation,[],[f45])).
% 1.78/0.60  % SZS output end Proof for theBenchmark
% 1.78/0.60  % (8905)------------------------------
% 1.78/0.60  % (8905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.60  % (8905)Termination reason: Refutation
% 1.78/0.60  
% 1.78/0.60  % (8905)Memory used [KB]: 11641
% 1.78/0.60  % (8905)Time elapsed: 0.150 s
% 1.78/0.60  % (8905)------------------------------
% 1.78/0.60  % (8905)------------------------------
% 1.78/0.60  % (8903)Success in time 0.238 s
%------------------------------------------------------------------------------
