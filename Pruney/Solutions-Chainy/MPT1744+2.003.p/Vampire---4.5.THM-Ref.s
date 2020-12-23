%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 783 expanded)
%              Number of leaves         :   27 ( 415 expanded)
%              Depth                    :   24
%              Number of atoms          : 1082 (13995 expanded)
%              Number of equality atoms :   59 (  61 expanded)
%              Maximal formula depth    :   29 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f531,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f292,f323,f464,f471,f494,f510,f530])).

fof(f530,plain,
    ( ~ spl9_2
    | spl9_3
    | spl9_5
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | ~ spl9_2
    | spl9_3
    | spl9_5
    | spl9_26 ),
    inference(subsumption_resolution,[],[f526,f73])).

fof(f73,plain,(
    r1_tmap_1(sK1,sK0,sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
    ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)
    & r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & r1_tmap_1(sK1,sK0,sK4,sK5)
    & v5_pre_topc(sK3,sK2,sK1)
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f42,f41,f40,f39,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                                & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & r1_tmap_1(X1,X0,X4,X5)
                            & v5_pre_topc(X3,X2,X1)
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                & l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
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
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,sK0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X6)
                            & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & r1_tmap_1(X1,sK0,X4,X5)
                        & v5_pre_topc(X3,X2,X1)
                        & m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0))))
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & v1_funct_1(X3) )
            & l1_pre_topc(X2)
            & v2_pre_topc(X2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6)
                          & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5)))
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & r1_tmap_1(sK1,sK0,X4,X5)
                      & v5_pre_topc(X3,X2,sK1)
                      & m1_subset_1(X5,u1_struct_0(sK1)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
                  & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
              & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
              & v1_funct_1(X3) )
          & l1_pre_topc(X2)
          & v2_pre_topc(X2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6)
                        & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5)))
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & r1_tmap_1(sK1,sK0,X4,X5)
                    & v5_pre_topc(X3,X2,sK1)
                    & m1_subset_1(X5,u1_struct_0(sK1)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
                & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1))))
            & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1))
            & v1_funct_1(X3) )
        & l1_pre_topc(X2)
        & v2_pre_topc(X2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6)
                      & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5)))
                      & m1_subset_1(X6,u1_struct_0(sK2)) )
                  & r1_tmap_1(sK1,sK0,X4,X5)
                  & v5_pre_topc(X3,sK2,sK1)
                  & m1_subset_1(X5,u1_struct_0(sK1)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
              & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
          & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
          & v1_funct_1(X3) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6)
                    & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5)))
                    & m1_subset_1(X6,u1_struct_0(sK2)) )
                & r1_tmap_1(sK1,sK0,X4,X5)
                & v5_pre_topc(X3,sK2,sK1)
                & m1_subset_1(X5,u1_struct_0(sK1)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
            & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
        & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4),X6)
                  & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5)))
                  & m1_subset_1(X6,u1_struct_0(sK2)) )
              & r1_tmap_1(sK1,sK0,X4,X5)
              & v5_pre_topc(sK3,sK2,sK1)
              & m1_subset_1(X5,u1_struct_0(sK1)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
          & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
      & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4),X6)
                & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5)))
                & m1_subset_1(X6,u1_struct_0(sK2)) )
            & r1_tmap_1(sK1,sK0,X4,X5)
            & v5_pre_topc(sK3,sK2,sK1)
            & m1_subset_1(X5,u1_struct_0(sK1)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6)
              & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5)))
              & m1_subset_1(X6,u1_struct_0(sK2)) )
          & r1_tmap_1(sK1,sK0,sK4,X5)
          & v5_pre_topc(sK3,sK2,sK1)
          & m1_subset_1(X5,u1_struct_0(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
      & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6)
            & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5)))
            & m1_subset_1(X6,u1_struct_0(sK2)) )
        & r1_tmap_1(sK1,sK0,sK4,X5)
        & v5_pre_topc(sK3,sK2,sK1)
        & m1_subset_1(X5,u1_struct_0(sK1)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6)
          & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))
          & m1_subset_1(X6,u1_struct_0(sK2)) )
      & r1_tmap_1(sK1,sK0,sK4,sK5)
      & v5_pre_topc(sK3,sK2,sK1)
      & m1_subset_1(sK5,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6)
        & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))
        & m1_subset_1(X6,u1_struct_0(sK2)) )
   => ( ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)
      & r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))
      & m1_subset_1(sK6,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6)
                              & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & r1_tmap_1(X1,X0,X4,X5)
                          & v5_pre_topc(X3,X2,X1)
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                      & v1_funct_1(X4) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & l1_pre_topc(X2)
              & v2_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
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
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( l1_pre_topc(X2)
                  & v2_pre_topc(X2)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                          & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r1_tmap_1(X1,X0,X4,X5)
                                & v5_pre_topc(X3,X2,X1) )
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                   => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_tmap_1(X1,X0,X4,X5)
                              & v5_pre_topc(X3,X2,X1) )
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))
                                 => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tmap_1)).

fof(f526,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,sK5)
    | ~ spl9_2
    | spl9_3
    | spl9_5
    | spl9_26 ),
    inference(backward_demodulation,[],[f493,f521])).

fof(f521,plain,
    ( sK5 = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)
    | ~ spl9_2
    | spl9_3
    | spl9_5 ),
    inference(forward_demodulation,[],[f520,f459])).

fof(f459,plain,
    ( sK5 = k1_funct_1(sK3,sK6)
    | ~ spl9_2
    | spl9_5 ),
    inference(resolution,[],[f431,f104])).

fof(f104,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK8(X0,X1) != X0
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( sK8(X0,X1) = X0
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK8(X0,X1) != X0
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( sK8(X0,X1) = X0
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f431,plain,
    ( r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5))
    | ~ spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f430,f65])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f430,plain,
    ( r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5))
    | ~ v1_funct_1(sK3)
    | ~ spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f429,f66])).

fof(f66,plain,(
    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f429,plain,
    ( r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f428,f67])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f428,plain,
    ( r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl9_2
    | spl9_5 ),
    inference(subsumption_resolution,[],[f423,f155])).

fof(f155,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl9_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl9_5
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f423,plain,
    ( r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5))
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f421,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
      | r2_hidden(k1_funct_1(X3,X4),X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            | ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            | ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

fof(f421,plain,
    ( r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k1_tarski(sK5)))
    | ~ spl9_2 ),
    inference(forward_demodulation,[],[f75,f118])).

fof(f118,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_2
  <=> k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f75,plain,(
    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f520,plain,
    ( k1_funct_1(sK3,sK6) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)
    | spl9_3 ),
    inference(resolution,[],[f163,f74])).

fof(f74,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f163,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK2))
        | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3) )
    | spl9_3 ),
    inference(subsumption_resolution,[],[f162,f123])).

fof(f123,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl9_3
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f162,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f161,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3)
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f137,f66])).

fof(f137,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK2))
      | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f67,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f493,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | spl9_26 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl9_26
  <=> r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f510,plain,(
    ~ spl9_1 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f508,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f508,plain,
    ( v2_struct_0(sK1)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f507,f108])).

fof(f108,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f61,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f507,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_1 ),
    inference(resolution,[],[f114,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f114,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl9_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f494,plain,
    ( ~ spl9_23
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f448,f491,f455,f451])).

fof(f451,plain,
    ( spl9_23
  <=> m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f455,plain,
    ( spl9_24
  <=> r1_tmap_1(sK2,sK1,sK3,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f448,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f447,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f447,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f446,f57])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f446,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f445,f58])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f445,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f444,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f444,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f443,f63])).

fof(f63,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f443,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f442,f64])).

fof(f64,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f442,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f441,f59])).

fof(f441,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f440,f60])).

fof(f60,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f440,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f439,f61])).

fof(f439,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f438,f65])).

fof(f438,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f437,f66])).

fof(f437,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f436,f67])).

fof(f436,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f435,f68])).

fof(f68,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f435,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f434,f69])).

fof(f69,plain,(
    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f434,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f433,f70])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f433,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f432,f74])).

fof(f432,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))
    | ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_1(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f76,f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5))
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
      | ~ r1_tmap_1(X2,X0,X4,X6)
      | ~ r1_tmap_1(X1,X2,X3,X5)
      | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)
                              | ~ r1_tmap_1(X2,X0,X4,X6)
                              | ~ r1_tmap_1(X1,X2,X3,X5)
                              | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                  | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  | ~ v1_funct_1(X3) )
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
                    & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X2))
                             => ( ( r1_tmap_1(X2,X0,X4,X6)
                                  & r1_tmap_1(X1,X2,X3,X5)
                                  & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6 )
                               => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).

fof(f76,plain,(
    ~ r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f471,plain,(
    spl9_24 ),
    inference(avatar_contradiction_clause,[],[f470])).

fof(f470,plain,
    ( $false
    | spl9_24 ),
    inference(subsumption_resolution,[],[f469,f74])).

fof(f469,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | spl9_24 ),
    inference(resolution,[],[f457,f150])).

fof(f150,plain,(
    ! [X0] :
      ( r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f149,f59])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f148,f60])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f147,f61])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f146,f62])).

fof(f146,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f145,f63])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f144,f64])).

fof(f144,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f143,f65])).

fof(f143,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f142,f66])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f134,f72])).

fof(f72,plain,(
    v5_pre_topc(sK3,sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v5_pre_topc(sK3,sK2,sK1)
      | r1_tmap_1(sK2,sK1,sK3,X0)
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK3)
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | v2_struct_0(sK2)
      | ~ l1_pre_topc(sK1)
      | ~ v2_pre_topc(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f67,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ v5_pre_topc(X2,X1,X0)
      | r1_tmap_1(X1,X0,X2,X4)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ( ~ r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2))
                    & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tmap_1(X1,X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X4] :
                      ( r1_tmap_1(X1,X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X1,X0)
                  | ? [X3] :
                      ( ~ r1_tmap_1(X1,X0,X2,X3)
                      & m1_subset_1(X3,u1_struct_0(X1)) ) )
                & ( ! [X3] :
                      ( r1_tmap_1(X1,X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                  | ~ v5_pre_topc(X2,X1,X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f457,plain,
    ( ~ r1_tmap_1(sK2,sK1,sK3,sK6)
    | spl9_24 ),
    inference(avatar_component_clause,[],[f455])).

fof(f464,plain,
    ( spl9_3
    | spl9_23 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl9_3
    | spl9_23 ),
    inference(subsumption_resolution,[],[f461,f74])).

fof(f461,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | spl9_3
    | spl9_23 ),
    inference(resolution,[],[f166,f453])).

fof(f453,plain,
    ( ~ m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f451])).

fof(f166,plain,
    ( ! [X4] :
        ( m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK2)) )
    | spl9_3 ),
    inference(subsumption_resolution,[],[f165,f123])).

fof(f165,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1))
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f164,f65])).

fof(f164,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f138,f66])).

fof(f138,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1))
      | ~ v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
      | ~ v1_funct_1(sK3)
      | v1_xboole_0(u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f67,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).

fof(f323,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f322,f116,f112])).

fof(f322,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f71,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f292,plain,(
    ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f290,f59])).

fof(f290,plain,
    ( v2_struct_0(sK1)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f289,f108])).

fof(f289,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f279,f77])).

fof(f77,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f279,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_5 ),
    inference(superposition,[],[f80,f156])).

fof(f156,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f154])).

fof(f133,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f131,f62])).

fof(f131,plain,
    ( v2_struct_0(sK2)
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f130,f109])).

fof(f109,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f64,f78])).

fof(f130,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl9_3 ),
    inference(resolution,[],[f124,f80])).

fof(f124,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (16762)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.47  % (16778)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.49  % (16768)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.49  % (16760)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (16763)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (16760)Refutation not found, incomplete strategy% (16760)------------------------------
% 0.20/0.50  % (16760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (16760)Memory used [KB]: 1791
% 0.20/0.50  % (16760)Time elapsed: 0.091 s
% 0.20/0.50  % (16760)------------------------------
% 0.20/0.50  % (16760)------------------------------
% 0.20/0.50  % (16777)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.50  % (16753)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (16769)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (16765)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (16755)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (16775)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (16754)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16764)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.51  % (16757)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (16761)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (16759)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (16767)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.53  % (16766)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (16756)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (16758)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (16776)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.53  % (16753)Refutation not found, incomplete strategy% (16753)------------------------------
% 0.20/0.53  % (16753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16753)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16753)Memory used [KB]: 10746
% 0.20/0.53  % (16753)Time elapsed: 0.106 s
% 0.20/0.53  % (16753)------------------------------
% 0.20/0.53  % (16753)------------------------------
% 0.20/0.53  % (16772)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.53  % (16773)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.53  % (16754)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f531,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f133,f292,f323,f464,f471,f494,f510,f530])).
% 0.20/0.53  fof(f530,plain,(
% 0.20/0.53    ~spl9_2 | spl9_3 | spl9_5 | spl9_26),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f529])).
% 0.20/0.53  fof(f529,plain,(
% 0.20/0.53    $false | (~spl9_2 | spl9_3 | spl9_5 | spl9_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f526,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    r1_tmap_1(sK1,sK0,sK4,sK5)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    ((((((~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) & r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(sK6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,sK5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f17,f42,f41,f40,f39,f38,f37,f36])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,sK0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,X2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,sK0,k1_partfun1(u1_struct_0(X2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,X2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(sK1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f39,plain,(
% 0.20/0.53    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),X3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(X3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) & v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,X4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(X4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) & v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) & v1_funct_1(sK4))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ? [X5] : (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),X5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,X5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(X5,u1_struct_0(sK1))) => (? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(X6,u1_struct_0(sK2))) & r1_tmap_1(sK1,sK0,sK4,sK5) & v5_pre_topc(sK3,sK2,sK1) & m1_subset_1(sK5,u1_struct_0(sK1)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    ? [X6] : (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(X6,u1_struct_0(sK2))) => (~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6) & r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5))) & m1_subset_1(sK6,u1_struct_0(sK2)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) & m1_subset_1(X6,u1_struct_0(X2))) & r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) & l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((? [X6] : ((~r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6) & r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5)))) & m1_subset_1(X6,u1_struct_0(X2))) & (r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1))) & m1_subset_1(X5,u1_struct_0(X1))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3))) & (l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f14])).
% 0.20/0.53  fof(f14,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((r1_tmap_1(X1,X0,X4,X5) & v5_pre_topc(X3,X2,X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (r2_hidden(X6,k8_relset_1(u1_struct_0(X2),u1_struct_0(X1),X3,k6_domain_1(u1_struct_0(X1),X5))) => r1_tmap_1(X2,X0,k1_partfun1(u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X3,X4),X6))))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_tmap_1)).
% 0.20/0.53  fof(f526,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,sK5) | (~spl9_2 | spl9_3 | spl9_5 | spl9_26)),
% 0.20/0.53    inference(backward_demodulation,[],[f493,f521])).
% 0.20/0.53  fof(f521,plain,(
% 0.20/0.53    sK5 = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6) | (~spl9_2 | spl9_3 | spl9_5)),
% 0.20/0.53    inference(forward_demodulation,[],[f520,f459])).
% 0.20/0.53  fof(f459,plain,(
% 0.20/0.53    sK5 = k1_funct_1(sK3,sK6) | (~spl9_2 | spl9_5)),
% 0.20/0.53    inference(resolution,[],[f431,f104])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.20/0.53    inference(equality_resolution,[],[f89])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f51])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK8(X0,X1) != X0 | ~r2_hidden(sK8(X0,X1),X1)) & (sK8(X0,X1) = X0 | r2_hidden(sK8(X0,X1),X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.53    inference(rectify,[],[f48])).
% 0.20/0.53  fof(f48,plain,(
% 0.20/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.20/0.53    inference(nnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.53  fof(f431,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5)) | (~spl9_2 | spl9_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f430,f65])).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f430,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5)) | ~v1_funct_1(sK3) | (~spl9_2 | spl9_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f429,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f429,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | (~spl9_2 | spl9_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f428,f67])).
% 0.20/0.53  fof(f67,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f428,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | (~spl9_2 | spl9_5)),
% 0.20/0.53    inference(subsumption_resolution,[],[f423,f155])).
% 0.20/0.53  fof(f155,plain,(
% 0.20/0.53    k1_xboole_0 != u1_struct_0(sK1) | spl9_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f154])).
% 0.20/0.53  fof(f154,plain,(
% 0.20/0.53    spl9_5 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.53  fof(f423,plain,(
% 0.20/0.53    r2_hidden(k1_funct_1(sK3,sK6),k1_tarski(sK5)) | k1_xboole_0 = u1_struct_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~spl9_2),
% 0.20/0.53    inference(resolution,[],[f421,f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) | r2_hidden(k1_funct_1(X3,X4),X2) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (! [X4] : ((r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) | ~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0)) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f54])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (! [X4] : ((r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) | (~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0))) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.53    inference(nnf_transformation,[],[f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.53    inference(flattening,[],[f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) | k1_xboole_0 = X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).
% 0.20/0.53  fof(f421,plain,(
% 0.20/0.53    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k1_tarski(sK5))) | ~spl9_2),
% 0.20/0.53    inference(forward_demodulation,[],[f75,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5) | ~spl9_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f116])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    spl9_2 <=> k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    r2_hidden(sK6,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK1),sK3,k6_domain_1(u1_struct_0(sK1),sK5)))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f520,plain,(
% 0.20/0.53    k1_funct_1(sK3,sK6) = k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6) | spl9_3),
% 0.20/0.53    inference(resolution,[],[f163,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    m1_subset_1(sK6,u1_struct_0(sK2))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3)) ) | spl9_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f162,f123])).
% 0.20/0.53  fof(f123,plain,(
% 0.20/0.53    ~v1_xboole_0(u1_struct_0(sK2)) | spl9_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f122])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    spl9_3 <=> v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f161,f65])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f137,f66])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK2)) | k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X3) = k1_funct_1(sK3,X3) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.53    inference(resolution,[],[f67,f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.53  fof(f493,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | spl9_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f491])).
% 0.20/0.53  fof(f491,plain,(
% 0.20/0.53    spl9_26 <=> r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.20/0.53  fof(f510,plain,(
% 0.20/0.53    ~spl9_1),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f509])).
% 0.20/0.53  fof(f509,plain,(
% 0.20/0.53    $false | ~spl9_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f508,f59])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f508,plain,(
% 0.20/0.53    v2_struct_0(sK1) | ~spl9_1),
% 0.20/0.53    inference(subsumption_resolution,[],[f507,f108])).
% 0.20/0.53  fof(f108,plain,(
% 0.20/0.53    l1_struct_0(sK1)),
% 0.20/0.53    inference(resolution,[],[f61,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    l1_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f507,plain,(
% 0.20/0.53    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl9_1),
% 0.20/0.53    inference(resolution,[],[f114,f80])).
% 0.20/0.53  fof(f80,plain,(
% 0.20/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    v1_xboole_0(u1_struct_0(sK1)) | ~spl9_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f112])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    spl9_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.53  fof(f494,plain,(
% 0.20/0.53    ~spl9_23 | ~spl9_24 | ~spl9_26),
% 0.20/0.53    inference(avatar_split_clause,[],[f448,f491,f455,f451])).
% 0.20/0.53  fof(f451,plain,(
% 0.20/0.53    spl9_23 <=> m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.20/0.53  fof(f455,plain,(
% 0.20/0.53    spl9_24 <=> r1_tmap_1(sK2,sK1,sK3,sK6)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.20/0.53  fof(f448,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1))),
% 0.20/0.53    inference(subsumption_resolution,[],[f447,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f447,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f446,f57])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f446,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f445,f58])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f445,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f444,f62])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    ~v2_struct_0(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f444,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f443,f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    v2_pre_topc(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f443,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f442,f64])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    l1_pre_topc(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f442,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f441,f59])).
% 0.20/0.53  fof(f441,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f440,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    v2_pre_topc(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f440,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f439,f61])).
% 0.20/0.53  fof(f439,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f438,f65])).
% 0.20/0.53  fof(f438,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f437,f66])).
% 0.20/0.53  fof(f437,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f436,f67])).
% 0.20/0.53  fof(f436,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f435,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    v1_funct_1(sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f435,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f434,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f434,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f433,f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f433,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(subsumption_resolution,[],[f432,f74])).
% 0.20/0.53  fof(f432,plain,(
% 0.20/0.53    ~r1_tmap_1(sK1,sK0,sK4,k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6)) | ~r1_tmap_1(sK2,sK1,sK3,sK6) | ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | ~m1_subset_1(sK6,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK4,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.53    inference(resolution,[],[f76,f101])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) | ~r1_tmap_1(X1,X2,X3,X5) | ~m1_subset_1(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5),u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(equality_resolution,[],[f81])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | ~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5) | (~r1_tmap_1(X2,X0,X4,X6) | ~r1_tmap_1(X1,X2,X3,X5) | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) != X6)) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) | ~v1_funct_1(X3))) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f13])).
% 0.20/0.53  fof(f13,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2) & ~v2_struct_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X0)) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X0,X4,X6) & r1_tmap_1(X1,X2,X3,X5) & k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5) = X6) => r1_tmap_1(X1,X0,k1_partfun1(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X2),u1_struct_0(X0),X3,X4),X5)))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tmap_1)).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ~r1_tmap_1(sK2,sK0,k1_partfun1(u1_struct_0(sK2),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK3,sK4),sK6)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f471,plain,(
% 0.20/0.53    spl9_24),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f470])).
% 0.20/0.53  fof(f470,plain,(
% 0.20/0.53    $false | spl9_24),
% 0.20/0.53    inference(subsumption_resolution,[],[f469,f74])).
% 0.20/0.53  fof(f469,plain,(
% 0.20/0.53    ~m1_subset_1(sK6,u1_struct_0(sK2)) | spl9_24),
% 0.20/0.53    inference(resolution,[],[f457,f150])).
% 0.20/0.53  fof(f150,plain,(
% 0.20/0.53    ( ! [X0] : (r1_tmap_1(sK2,sK1,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f149,f59])).
% 0.20/0.53  fof(f149,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f148,f60])).
% 0.20/0.53  fof(f148,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f147,f61])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f146,f62])).
% 0.20/0.53  fof(f146,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f145,f63])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f144,f64])).
% 0.20/0.53  fof(f144,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f143,f65])).
% 0.20/0.53  fof(f143,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f142,f66])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f134,f72])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    v5_pre_topc(sK3,sK2,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f134,plain,(
% 0.20/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~v5_pre_topc(sK3,sK2,sK1) | r1_tmap_1(sK2,sK1,sK3,X0) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1)) )),
% 0.20/0.53    inference(resolution,[],[f67,f82])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~v5_pre_topc(X2,X1,X0) | r1_tmap_1(X1,X0,X2,X4) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | (~r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_tmap_1(X1,X0,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_tmap_1(X1,X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(rectify,[],[f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X1,X0) | ? [X3] : (~r1_tmap_1(X1,X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~v5_pre_topc(X2,X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(nnf_transformation,[],[f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X1,X0) <=> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.20/0.53  fof(f457,plain,(
% 0.20/0.53    ~r1_tmap_1(sK2,sK1,sK3,sK6) | spl9_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f455])).
% 0.20/0.53  fof(f464,plain,(
% 0.20/0.53    spl9_3 | spl9_23),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f463])).
% 0.20/0.53  fof(f463,plain,(
% 0.20/0.53    $false | (spl9_3 | spl9_23)),
% 0.20/0.53    inference(subsumption_resolution,[],[f461,f74])).
% 0.20/0.53  fof(f461,plain,(
% 0.20/0.53    ~m1_subset_1(sK6,u1_struct_0(sK2)) | (spl9_3 | spl9_23)),
% 0.20/0.53    inference(resolution,[],[f166,f453])).
% 0.20/0.53  fof(f453,plain,(
% 0.20/0.53    ~m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,sK6),u1_struct_0(sK1)) | spl9_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f451])).
% 0.20/0.53  fof(f166,plain,(
% 0.20/0.53    ( ! [X4] : (m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1)) | ~m1_subset_1(X4,u1_struct_0(sK2))) ) | spl9_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f165,f123])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f164,f65])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.53    inference(subsumption_resolution,[],[f138,f66])).
% 0.20/0.53  fof(f138,plain,(
% 0.20/0.53    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | m1_subset_1(k3_funct_2(u1_struct_0(sK2),u1_struct_0(sK1),sK3,X4),u1_struct_0(sK1)) | ~v1_funct_2(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~v1_funct_1(sK3) | v1_xboole_0(u1_struct_0(sK2))) )),
% 0.20/0.53    inference(resolution,[],[f67,f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => m1_subset_1(k3_funct_2(X0,X1,X2,X3),X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_funct_2)).
% 0.20/0.53  fof(f323,plain,(
% 0.20/0.53    spl9_1 | spl9_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f322,f116,f112])).
% 0.20/0.53  fof(f322,plain,(
% 0.20/0.53    k6_domain_1(u1_struct_0(sK1),sK5) = k1_tarski(sK5) | v1_xboole_0(u1_struct_0(sK1))),
% 0.20/0.53    inference(resolution,[],[f71,f88])).
% 0.20/0.53  fof(f88,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.53    inference(flattening,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    m1_subset_1(sK5,u1_struct_0(sK1))),
% 0.20/0.53    inference(cnf_transformation,[],[f43])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    ~spl9_5),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f291])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    $false | ~spl9_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f290,f59])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    v2_struct_0(sK1) | ~spl9_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f289,f108])).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl9_5),
% 0.20/0.53    inference(subsumption_resolution,[],[f279,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f279,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl9_5),
% 0.20/0.53    inference(superposition,[],[f80,f156])).
% 0.20/0.53  fof(f156,plain,(
% 0.20/0.53    k1_xboole_0 = u1_struct_0(sK1) | ~spl9_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f154])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    ~spl9_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    $false | ~spl9_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f131,f62])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    v2_struct_0(sK2) | ~spl9_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f130,f109])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    l1_struct_0(sK2)),
% 0.20/0.53    inference(resolution,[],[f64,f78])).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl9_3),
% 0.20/0.53    inference(resolution,[],[f124,f80])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    v1_xboole_0(u1_struct_0(sK2)) | ~spl9_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f122])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (16754)------------------------------
% 0.20/0.53  % (16754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16754)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (16754)Memory used [KB]: 11001
% 0.20/0.53  % (16754)Time elapsed: 0.101 s
% 0.20/0.53  % (16754)------------------------------
% 0.20/0.53  % (16754)------------------------------
% 0.20/0.54  % (16752)Success in time 0.179 s
%------------------------------------------------------------------------------
